/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Native
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Plan
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Transform

/-! # Scalar carry-less additive butterflies over contiguous word rows -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace AdditiveNTT.Packed.Scalar

open BF64
open AdditiveNTT.Bitsliced (fold fold_eq)
open AdditiveNTT.Bitsliced.Native

/-- A machine traversal of a bounded number of words. -/
@[specialize] def foldSmall (n : Nat) (hn : n < 4294967296)
    (f : (i : USize) → i.toNat < n → α → α) (a : α) : α :=
  fold (USize.ofNat n) (fun i hi a => f i (by
    have h := USize.lt_iff_toNat_lt.mp hi
    rwa [ofNat_toNat n hn] at h) a) a

/-- The machine traversal visits the same coordinates as a finite fold. -/
theorem foldSmall_eq (n : Nat) (hn : n < 4294967296)
    (f : (i : USize) → i.toNat < n → α → α) (a : α) :
    foldSmall n hn f a = Fin.foldl n (fun a i =>
      f (USize.ofNat i.val) (by rw [ofNat_toNat _ (by omega)]; exact i.isLt) a) a := by
  unfold foldSmall
  rw [fold_eq]
  simp only [ofNat_toNat n hn, Fin.val_cast]

/-- A bounded machine product is its natural-number product. -/
theorem mul_toNat (i j : USize) (h : i.toNat * j.toNat < 4294967296) :
    (i * j).toNat = i.toNat * j.toNat := by
  rw [USize.toNat_mul, Nat.mod_eq_of_lt (lt_of_lt_of_le h USize.le_size)]

/-- One scalar butterfly reads both words before either store. -/
@[inline] def butterfly (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (lo hi : USize) (hlo : lo.toNat < n) (hhi : hi.toNat < n) (t : UInt64) :
    BF64.Packed.Buffer n :=
  let u := read a hn lo hlo
  let v := read a hn hi hhi
  let next := u ^^^ (Word.mulMasked ⟨t⟩ ⟨v⟩).val
  write (write a hn lo hlo next) hn hi hhi (next ^^^ v)

/-- Scalar word stores are the certified packed forward butterfly. -/
theorem butterfly_eq (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (lo hi : USize) (hlo : lo.toNat < n) (hhi : hi.toNat < n) (t : UInt64) :
    butterfly a hn lo hi hlo hhi t =
      let u := BF64.Packed.read a ⟨lo.toNat, hlo⟩
      let v := BF64.Packed.read a ⟨hi.toNat, hhi⟩
      let out := forwardPair (Multiplier.masked ⟨t⟩) u v
      BF64.Packed.write (BF64.Packed.write a ⟨lo.toNat, hlo⟩ out.1)
        ⟨hi.toNat, hhi⟩ out.2 := by
  simp only [butterfly, read_eq, write_eq, forwardPair, Multiplier.masked, Word.add]

/-- Split a linear fold into contiguous blocks without changing update order. -/
theorem foldl_blocks (blocks width : Nat) (f : α → Fin (blocks * width) → α) (a : α) :
    Fin.foldl (blocks * width) f a =
      Fin.foldl blocks (fun a b => Fin.foldl width (fun a j =>
        f a ⟨j.val + width * b.val, by
          have := j.isLt
          have := b.isLt
          nlinarith⟩) a) a := by
  induction blocks generalizing a with
  | zero => simp only [Nat.zero_mul, Fin.foldl_zero]
  | succ blocks ih =>
    rw [Fin.foldl_succ_last]
    have he : (blocks + 1) * width = blocks * width + width := by ring
    rw [Fin.foldl_congr he, Fin.foldl_add]
    rw [ih]
    simp only [Fin.cast, Fin.natAdd, Fin.castLE, Fin.castSucc, Fin.last,
      Fin.castAdd, Nat.mul_comm, Nat.add_comm]

/-- One shared-scalar stage, with contiguous word sweeps and machine addresses. -/
def forwardStage (p : Bitsliced.Plan β d hd) (i : Fin d) (lanes : Nat)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    BF64.Packed.Buffer (2 ^ d * lanes) :=
  let span := 2 ^ i.val * lanes
  let blocks := 2 ^ (d - i.val - 1)
  have hcount : blocks * (2 * span) = 2 ^ d * lanes := stage_word_count d i lanes
  have hpos : 0 < span := Nat.mul_pos (by positivity) hlanes
  have hb : blocks < 4294967296 := by nlinarith
  have hs : span < 4294967296 := by
    have hblocks : 0 < blocks := by dsimp [blocks]; positivity
    nlinarith
  let stride := USize.ofNat span
  have hstride : stride.toNat = span := ofNat_toNat _ hs
  have hdouble : (stride + stride).toNat = 2 * span := by
    rw [add_toNat _ _ (by
      rw [hstride]
      have hblocks : 0 < blocks := by dsimp [blocks]; positivity
      nlinarith), hstride]
    omega
  foldSmall blocks hb (fun u hu a =>
    let t := (p.get i ⟨u.toNat, hu⟩).val
    let base := u * (stride + stride)
    have hbase : base.toNat = u.toNat * (2 * span) := by
      rw [mul_toNat _ _ (by rw [hdouble]; nlinarith), hdouble]
    foldSmall span hs (fun j hj a =>
      let lo := base + j
      let hi := lo + stride
      have hlow : lo.toNat = u.toNat * (2 * span) + j.toNat := by
        rw [add_toNat _ _ (by rw [hbase]; nlinarith), hbase]
      have hhigh : hi.toNat = u.toNat * (2 * span) + j.toNat + span := by
        rw [add_toNat _ _ (by rw [hlow, hstride]; nlinarith), hlow, hstride]
      butterfly a hn lo hi (by rw [hlow]; nlinarith) (by rw [hhigh]; nlinarith) t) a) a

/-- A fixed-size byte array, with no runtime word-count field. -/
abbrev Bytes (n : Nat) := {a : ByteArray // a.size = 8 * n}

/-- Expose contiguous bytes outside the butterfly loop. -/
@[inline] def unpack (a : BF64.Packed.Buffer n) : Bytes n :=
  ⟨a.val.bytes, by rw [a.val.byteSize, a.property]⟩

/-- Restore the packed interface after the butterfly loop. -/
@[inline] def pack (a : Bytes n) : BF64.Packed.Buffer n := ⟨⟨n, a.val, a.property⟩, rfl⟩

@[simp] theorem pack_unpack (a : BF64.Packed.Buffer n) : pack (unpack a) = a := by
  rcases a with ⟨⟨sz, bytes, hb⟩, hs⟩
  change sz = n at hs
  subst sz
  rfl

/-- A scalar butterfly whose accumulator is only the contiguous byte array. -/
@[inline] def butterflyBytes (a : Bytes n) (hn : 8 * n < 4294967296)
    (lo hi : USize) (hlo : lo.toNat < n) (hhi : hi.toNat < n) (t : UInt64) : Bytes n :=
  unpack (butterfly (pack a) hn lo hi hlo hhi t)

/-- Packing commutes with one byte-array butterfly. -/
@[simp] theorem pack_butterflyBytes (a : Bytes n) (hn : 8 * n < 4294967296)
    (lo hi : USize) (hlo : lo.toNat < n) (hhi : hi.toNat < n) (t : UInt64) :
    pack (butterflyBytes a hn lo hi hlo hhi t) = butterfly (pack a) hn lo hi hlo hhi t :=
  pack_unpack _

/-- A traversal commutes with any accumulator representation preserving its updates. -/
theorem foldSmall_hom {α γ : Type*} (n : Nat) (hn : n < 4294967296) (g : α → γ)
    (f : (i : USize) → i.toNat < n → α → α)
    (f' : (i : USize) → i.toNat < n → γ → γ)
    (h : ∀ i hi a, g (f i hi a) = f' i hi (g a)) (a : α) :
    g (foldSmall n hn f a) = foldSmall n hn f' (g a) := by
  simp only [foldSmall_eq, Fin.foldl_eq_finRange_foldl]
  exact (List.foldl_hom (f := g) (fun a i => (h _ _ a).symm)).symm

/-- One shared-scalar stage, with contiguous word sweeps and machine addresses. -/
def forwardStageBytes (p : Bitsliced.Plan β d hd) (i : Fin d) (lanes : Nat)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    BF64.Packed.Buffer (2 ^ d * lanes) :=
  let span := 2 ^ i.val * lanes
  let blocks := 2 ^ (d - i.val - 1)
  have hcount : blocks * (2 * span) = 2 ^ d * lanes := stage_word_count d i lanes
  have hpos : 0 < span := Nat.mul_pos (by positivity) hlanes
  have hb : blocks < 4294967296 := by nlinarith
  have hs : span < 4294967296 := by
    have hblocks : 0 < blocks := by dsimp [blocks]; positivity
    nlinarith
  let stride := USize.ofNat span
  have hstride : stride.toNat = span := ofNat_toNat _ hs
  have hdouble : (stride + stride).toNat = 2 * span := by
    rw [add_toNat _ _ (by
      rw [hstride]
      have hblocks : 0 < blocks := by dsimp [blocks]; positivity
      nlinarith), hstride]
    omega
  pack <| foldSmall blocks hb (fun u hu a =>
    let t := (p.get i ⟨u.toNat, hu⟩).val
    let base := u * (stride + stride)
    have hbase : base.toNat = u.toNat * (2 * span) := by
      rw [mul_toNat _ _ (by rw [hdouble]; nlinarith), hdouble]
    foldSmall span hs (fun j hj a =>
      let lo := base + j
      let hi := lo + stride
      have hlow : lo.toNat = u.toNat * (2 * span) + j.toNat := by
        rw [add_toNat _ _ (by rw [hbase]; nlinarith), hbase]
      have hhigh : hi.toNat = u.toNat * (2 * span) + j.toNat + span := by
        rw [add_toNat _ _ (by rw [hlow, hstride]; nlinarith), hlow, hstride]
      butterflyBytes a hn lo hi (by rw [hlow]; nlinarith)
        (by rw [hhigh]; nlinarith) t) a) (unpack a)

/-- Machine-addressed scalar stages preserve the complete packed buffer. -/
theorem forwardStage_eq (p : Bitsliced.Plan β d hd) (i : Fin d) (lanes : Nat)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    forwardStage p i lanes hlanes a hn = Packed.forwardStage p.toPacked i lanes a := by
  unfold forwardStage Packed.forwardStage stageSweep
  rw [foldl_blocks]
  simp only [foldSmall_eq]
  congr 1
  funext a b
  congr 1
  funext a j
  have hs : 2 ^ i.val * lanes < 4294967296 := by
    have := stage_word_count d i lanes
    have : 0 < 2 ^ (d - i.val - 1) := by positivity
    nlinarith
  have hb : b.val < 4294967296 := by
    have := stage_word_count d i lanes
    have := b.isLt
    have : 0 < 2 ^ i.val * lanes := by positivity
    nlinarith
  have hj : j.val < 4294967296 := lt_trans j.isLt hs
  have hlo : b.val * (2 * (2 ^ i.val * lanes)) + j.val < 4294967296 := by
    have := stage_word_count d i lanes
    have := b.isLt
    have := j.isLt
    nlinarith
  have hhi : b.val * (2 * (2 ^ i.val * lanes)) + j.val + 2 ^ i.val * lanes <
      4294967296 := by
    have := stage_word_count d i lanes
    have := b.isLt
    have := j.isLt
    nlinarith
  simp only [← USize.ofNat_add, ← USize.ofNat_mul, ← two_mul, butterfly_eq,
    ofNat_toNat _ hlo, ofNat_toNat _ hhi, ofNat_toNat _ hb,
    Bitsliced.Plan.toPacked, Packed.Plan.get, Vector.getElem_ofFn, Array.getElem_ofFn,
    lowerIndex, upperIndex, Fin.divNat]
  simp only [Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ i.val * lanes),
    Nat.div_eq_of_lt j.isLt, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt j.isLt]
  simp only [Nat.mul_comm, Nat.add_comm]


/-- Packing a byte-array traversal lifts its updates to the packed interface. -/
theorem foldSmall_pack (n : Nat) (hn : n < 4294967296)
    (f : (i : USize) → i.toNat < n → Bytes m → Bytes m) (a : Bytes m) :
    pack (foldSmall n hn f a) = foldSmall n hn
      (fun i hi a => pack (f i hi (unpack a))) (pack a) := by
  apply foldSmall_hom
  intro i hi a
  rfl

/-- Byte-only accumulators preserve the complete packed stage. -/
@[csimp] theorem forwardStageBytes_eq : @forwardStage = @forwardStageBytes := by
  funext β d hd p i lanes hlanes a hn
  symm
  unfold forwardStageBytes forwardStage
  rw [foldSmall_pack, pack_unpack]
  congr 1
  funext u hu a
  rw [foldSmall_pack]
  simp only [pack_butterflyBytes, pack_unpack]

/-- Store into a byte-only loop accumulator. -/
@[inline] def writeBytes (a : Bytes n) (hn : 8 * n < 4294967296)
    (i : USize) (hi : i.toNat < n) (v : UInt64) : Bytes n :=
  unpack (write (pack a) hn i hi v)

@[simp] theorem pack_writeBytes (a : Bytes n) (hn : 8 * n < 4294967296)
    (i : USize) (hi : i.toNat < n) (v : UInt64) :
    pack (writeBytes a hn i hi v) = write (pack a) hn i hi v := pack_unpack _

/-- Descending scalar stages on word rows. -/
def forward (p : Bitsliced.Plan β d hd) (ell : Nat) (hell : ell ≤ d) (lanes : Nat)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  Fin.foldl ell (fun a k => forwardStage p ⟨ell - k.val - 1, by omega⟩ lanes hlanes a hn) a

/-- Descending machine sweeps preserve every packed transform prefix. -/
theorem forward_eq (p : Bitsliced.Plan β d hd) (ell : Nat) (hell : ell ≤ d) (lanes : Nat)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    forward p ell hell lanes hlanes a hn = Packed.forward p.toPacked ell hell lanes a := by
  simp only [forward, Packed.forward, forwardStage_eq]
/-- Fill word rows without converting loop coordinates to boxed naturals. -/
@[specialize] def tabulateUSize (n : Nat) (hn : 8 * n < 4294967296)
    (f : (i : USize) → i.toNat < n → UInt64) : BF64.Packed.Buffer n :=
  pack <| foldSmall n (by omega) (fun i hi a => writeBytes a hn i hi (f i hi))
    (unpack ⟨BF64.Packed.zeros n, rfl⟩)

/-- Unboxed input coordinates preserve the packed coordinate function. -/
theorem tabulateUSize_eq (n : Nat) (hn : 8 * n < 4294967296)
    (f : (i : USize) → i.toNat < n → UInt64) :
    tabulateUSize n hn f = Packed.tabulate n (fun i =>
      ⟨f (USize.ofNat i.val) (by
        rw [ofNat_toNat _ (by have := i.isLt; omega)]; exact i.isLt)⟩) := by
  unfold tabulateUSize Packed.tabulate
  rw [foldSmall_pack, pack_unpack, foldSmall_eq]
  simp (disch := omega) only [pack_writeBytes, pack_unpack, write_eq, ofNat_toNat]

/-- Replicate a row-major message using machine word counts. -/
@[noinline] def tileRowsSized (inputRows outputRows lanes : Nat) (hrows : 0 < inputRows)
    (hout : inputRows ≤ outputRows) (hlanes : 0 < lanes)
    (a : BF64.Packed.Buffer (inputRows * lanes))
    (hn : 8 * (outputRows * lanes) < 4294967296) :
    BF64.Packed.Buffer (outputRows * lanes) :=
  have hinput : 8 * (inputRows * lanes) < 4294967296 := by nlinarith
  let words := USize.ofNat (inputRows * lanes)
  have hw : words.toNat = inputRows * lanes := ofNat_toNat _ (by omega)
  tabulateUSize _ hn fun j hj =>
    read a hinput (j % words) (by
      rw [USize.toNat_mod, hw]
      exact Nat.mod_lt _ (Nat.mul_pos hrows hlanes))

/-- Replicate a row-major message into all evaluation cosets. -/
def tileRows (ell rate lanes : Nat) (hlanes : 0 < lanes)
    (a : BF64.Packed.Buffer (2 ^ ell * lanes))
    (hn : 8 * (2 ^ (ell + rate) * lanes) < 4294967296) :
    BF64.Packed.Buffer (2 ^ (ell + rate) * lanes) :=
  tileRowsSized (2 ^ ell) (2 ^ (ell + rate)) lanes (by positivity)
    (Nat.pow_le_pow_right (by decide) (by omega)) hlanes a hn

/-- Reverse lane-major columns with unboxed word addresses. -/
@[noinline] def tileLanesSized (inputRows outputRows live lanes : Nat) (hrows : 0 < inputRows)
    (hout : inputRows ≤ outputRows) (hlanes : 0 < lanes)
    (hlive : live ≤ lanes) (a : BF64.Packed.Buffer (live * inputRows))
    (hn : 8 * (outputRows * lanes) < 4294967296) :
    BF64.Packed.Buffer (outputRows * lanes) :=
  have hi : inputRows < 4294967296 := by nlinarith
  have hl : lanes < 4294967296 := by nlinarith
  have hinput : 8 * (live * inputRows) < 4294967296 := by nlinarith
  let rows := USize.ofNat inputRows
  let width := USize.ofNat lanes
  let padding := USize.ofNat (lanes - live)
  let last := USize.ofNat (lanes - 1)
  have hr : rows.toNat = inputRows := ofNat_toNat _ hi
  have hw : width.toNat = lanes := ofNat_toNat _ hl
  have hp : padding.toNat = lanes - live := ofNat_toNat _ (by omega)
  have ht : last.toNat = lanes - 1 := ofNat_toNat _ (by omega)
  tabulateUSize _ hn fun j hj =>
    let lane := j % width
    have hc : lane.toNat < lanes := by rw [USize.toNat_mod, hw]; exact Nat.mod_lt _ hlanes
    if h : lane < padding then 0 else
      let col := last - lane
      let row := j / width % rows
      have hcol : col.toNat = lanes - 1 - lane.toNat := by
        rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, ht]; omega), ht]
      have hrow : row.toNat < inputRows := by
        rw [USize.toNat_mod, hr]
        exact Nat.mod_lt _ hrows
      have hcl : col.toNat < live := by
        rw [USize.lt_iff_toNat_lt, hp] at h
        rw [hcol]
        omega
      let idx := col * rows + row
      have hprod : (col * rows).toNat = col.toNat * inputRows := by
        rw [mul_toNat _ _ (by rw [hr]; nlinarith), hr]
      have hidx : idx.toNat = col.toNat * inputRows + row.toNat := by
        rw [add_toNat _ _ (by rw [hprod]; nlinarith), hprod]
      read a hinput idx (by rw [hidx]; nlinarith)

/-- Reverse live lane-major K columns into rows, with absent lanes leading. -/
def tileLanes (ell rate live lanes : Nat) (hlanes : 0 < lanes) (hlive : live ≤ lanes)
    (a : BF64.Packed.Buffer (live * 2 ^ ell))
    (hn : 8 * (2 ^ (ell + rate) * lanes) < 4294967296) :
    BF64.Packed.Buffer (2 ^ (ell + rate) * lanes) :=
  tileLanesSized (2 ^ ell) (2 ^ (ell + rate)) live lanes (by positivity)
    (Nat.pow_le_pow_right (by decide) (by omega)) hlanes hlive a hn

/-- Machine input tiling preserves the certified row-major input. -/
theorem tileRows_eq (ell rate lanes : Nat) (hlanes : 0 < lanes)
    (a : BF64.Packed.Buffer (2 ^ ell * lanes))
    (hn : 8 * (2 ^ (ell + rate) * lanes) < 4294967296) :
    tileRows ell rate lanes hlanes a hn = Packed.tileRows ell rate lanes a := by
  unfold tileRows tileRowsSized Packed.tileRows
  rw [tabulateUSize_eq]
  congr 1
  funext j
  have he : 2 ^ ell ≤ 2 ^ (ell + rate) := Nat.pow_le_pow_right (by decide) (by omega)
  have hj : j.val < 4294967296 := by have := j.isLt; omega
  have hi : 2 ^ ell * lanes < 4294967296 := by nlinarith
  simp only [read_eq, USize.toNat_mod, ofNat_toNat _ hj, ofNat_toNat _ hi]

/-- Machine input tiling preserves every reversed and padded lane. -/
theorem tileLanes_eq (ell rate live lanes : Nat) (hlanes : 0 < lanes) (hlive : live ≤ lanes)
    (a : BF64.Packed.Buffer (live * 2 ^ ell))
    (hn : 8 * (2 ^ (ell + rate) * lanes) < 4294967296) :
    tileLanes ell rate live lanes hlanes hlive a hn =
      Packed.tileLanes ell rate live lanes hlive a := by
  unfold tileLanes tileLanesSized Packed.tileLanes
  rw [tabulateUSize_eq]
  congr 1
  funext j
  have he : 2 ^ ell ≤ 2 ^ (ell + rate) := Nat.pow_le_pow_right (by decide) (by omega)
  have hj : j.val < 4294967296 := by have := j.isLt; omega
  have hl : lanes < 4294967296 := by have := Nat.one_le_two_pow (n := ell + rate); nlinarith
  have hr : 2 ^ ell < 4294967296 := by nlinarith
  have hp : lanes - live < 4294967296 := by omega
  have ht : lanes - 1 < 4294967296 := by omega
  simp only [USize.lt_iff_toNat_lt, USize.toNat_mod, ofNat_toNat _ hj,
    ofNat_toNat _ hl, ofNat_toNat _ hp]
  split
  · rfl
  · rename_i h
    simp only [read_eq, USize.toNat_add, USize.toNat_mul, USize.toNat_div,
      USize.toNat_mod, ofNat_toNat _ hj, ofNat_toNat _ hl, ofNat_toNat _ hr]
    have hc : j.val % lanes < lanes := Nat.mod_lt _ hlanes
    have hsub : (USize.ofNat (lanes - 1) - USize.ofNat j.val % USize.ofNat lanes).toNat =
        lanes - 1 - j.val % lanes := by
      rw [USize.toNat_sub_of_le _ _ (by
        rw [USize.le_iff_toNat_le, USize.toNat_mod, ofNat_toNat _ hj,
          ofNat_toNat _ hl, ofNat_toNat _ ht]
        omega), ofNat_toNat _ ht, USize.toNat_mod, ofNat_toNat _ hj, ofNat_toNat _ hl]
    have hcol : lanes - 1 - j.val % lanes < live := by omega
    have hrow : j.val / lanes % 2 ^ ell < 2 ^ ell := Nat.mod_lt _ (by positivity)
    have hsize : 8 * (live * 2 ^ ell) < 4294967296 := by
      have hm := Nat.mul_le_mul hlive he
      nlinarith
    have hm : (lanes - 1 - j.val % lanes) * 2 ^ ell < 2 ^ System.Platform.numBits :=
      lt_of_lt_of_le (by nlinarith) USize.le_size
    have ha : (lanes - 1 - j.val % lanes) * 2 ^ ell + j.val / lanes % 2 ^ ell <
        2 ^ System.Platform.numBits := lt_of_lt_of_le (by nlinarith) USize.le_size
    simp only [hsub, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt ha]

end AdditiveNTT.Packed.Scalar
