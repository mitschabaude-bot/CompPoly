/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.StripsCorrectness
import all CompPoly.Univariate.NTTFast.Plan
import all CompPoly.Univariate.NTTFast.Packed.Strips
import all CompPoly.Univariate.NTTFast.Packed.Native
import CompPoly.Univariate.NTTFast.Packed.Unrolled
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! # Correctness of the strip extension's coset blocks

A coset block's first layers read the strip's coefficients in bit-reversed order and multiply them
by the coset table (`Native.stripScaled_encode`); the gather copies eight words of each row of the
input chunks (`Native.stripOfChunks_rowChunks`) and the split transposes eight rows at a time
(`Native.stripColumns_encode`). Together with the transforms of `StripsCorrectness.lean`, block
`t` of a strip is its columns' blocks (`Native.stripBlock_stripCoefficients`).
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

section Kernels
open Montgomery.Native32 (Mont32Field FastField)
open CompPoly.PackedRepr (encode size_encode_uint32)

variable {p : ℕ} [Mont32Field p]

/-! ### Coset blocks -/

/-- The coset product of a strip's coefficients `C`, stored in bit-reversed row order: row `i` is
row `bitrev i` of `C` times `T[i]`. -/
def scaledRows (T C : Array (FastField p)) (m : Nat) : Array (FastField p) :=
  Array.ofFn (n := 8 * 2 ^ m) fun i ↦
    T.getD (i.val / 8) 0 * C.getD (8 * NTT.Transform.bitRevNat m (i.val / 8) + i.val % 8) 0

/-- A coset block's first layers over a strip, the twiddle tables broadcast over the lanes: the
radix-two layer if `m` is odd, else the first radix-four pass. -/
def firstLayers (tw : Array (Array (FastField p))) (m : Nat) (X : Array (FastField p)) :
    Array (FastField p) :=
  if m % 2 = 1 then
    Plan.butterflyDIFInner (expand8 (tw.getD (m - 1) #[])) (8 * 2 ^ (m - 1)) 0 0
      (8 * 2 ^ (m - 1)) X
  else
    Plan.butterflyDIFRadix4Blocks (expand8 (tw.getD (m - 1) #[])) (expand8 (tw.getD (m - 2) #[]))
      (4 * (8 * 2 ^ (m - 2))) (8 * 2 ^ (m - 2)) 1 0 X

/-- Four rows `i0, …, i3` of eight words stored one after another. -/
def rows4 (v : Nat → Nat → UInt32) (i0 i1 i2 i3 : USize) (b : ByteArray) : ByteArray :=
  let b := Native.storeWords b (i0 * 4) 8 (v 0 0) (v 0 1) (v 0 2) (v 0 3)
    (v 0 4) (v 0 5) (v 0 6) (v 0 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b (i1 * 4) 8 (v 1 0) (v 1 1) (v 1 2) (v 1 3)
    (v 1 4) (v 1 5) (v 1 6) (v 1 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b (i2 * 4) 8 (v 2 0) (v 2 1) (v 2 2) (v 2 3)
    (v 2 4) (v 2 5) (v 2 6) (v 2 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b (i3 * 4) 8 (v 3 0) (v 3 1) (v 3 2) (v 3 3)
    (v 3 4) (v 3 5) (v 3 6) (v 3 7) 0 0 0 0 0 0 0 0
  b

/-- Two rows `i0`, `i1` of eight words stored one after another. -/
def rows2 (v : Nat → Nat → UInt32) (i0 i1 : USize) (b : ByteArray) : ByteArray :=
  let b := Native.storeWords b (i0 * 4) 8 (v 0 0) (v 0 1) (v 0 2) (v 0 3)
    (v 0 4) (v 0 5) (v 0 6) (v 0 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b (i1 * 4) 8 (v 1 0) (v 1 1) (v 1 2) (v 1 3)
    (v 1 4) (v 1 5) (v 1 6) (v 1 7) 0 0 0 0 0 0 0 0
  b

/-- Four rows, each stored with its targets, fill them. -/
theorem Native.fill_rows4 (Tg : Nat → UInt32) (N : Nat) (hN : 4 * N < USize.size)
    (v : Nat → Nat → UInt32) (i0 i1 i2 i3 : USize) (h0 : i0.toNat + 8 ≤ N)
    (h1 : i1.toNat + 8 ≤ N) (h2 : i2.toNat + 8 ≤ N) (h3 : i3.toNat + 8 ≤ N)
    (hv0 : ∀ l < 8, v 0 l = Tg (i0.toNat + l)) (hv1 : ∀ l < 8, v 1 l = Tg (i1.toNat + l))
    (hv2 : ∀ l < 8, v 2 l = Tg (i2.toNat + l)) (hv3 : ∀ l < 8, v 3 l = Tg (i3.toNat + l)) :
    Native.Fill Tg (fun k ↦ ((i0.toNat ≤ k ∧ k < i0.toNat + 8) ∨
      (i1.toNat ≤ k ∧ k < i1.toNat + 8)) ∨ (i2.toNat ≤ k ∧ k < i2.toNat + 8) ∨
      (i3.toNat ≤ k ∧ k < i3.toNat + 8)) N (rows4 v i0 i1 i2 i3) := by
  have f0 := Native.fill_storeWords8 Tg N (i0 * 4) _ (v 0) (Native.wordOffset_toNat' _ (by omega))
    hN h0 hv0
  have f1 := Native.fill_storeWords8 Tg N (i1 * 4) _ (v 1) (Native.wordOffset_toNat' _ (by omega))
    hN h1 hv1
  have f2 := Native.fill_storeWords8 Tg N (i2 * 4) _ (v 2) (Native.wordOffset_toNat' _ (by omega))
    hN h2 hv2
  have f3 := Native.fill_storeWords8 Tg N (i3 * 4) _ (v 3) (Native.wordOffset_toNat' _ (by omega))
    hN h3 hv3
  refine (((f0.comp f1).comp (f2.comp f3)).congr fun b ↦ ?_).mono ?_
  · simp only [Function.comp_apply, rows4]
  · intro k hk
    exact hk

/-- Two rows, each stored with its targets, fill them. -/
theorem Native.fill_rows2 (Tg : Nat → UInt32) (N : Nat) (hN : 4 * N < USize.size)
    (v : Nat → Nat → UInt32) (i0 i1 : USize) (h0 : i0.toNat + 8 ≤ N) (h1 : i1.toNat + 8 ≤ N)
    (hv0 : ∀ l < 8, v 0 l = Tg (i0.toNat + l)) (hv1 : ∀ l < 8, v 1 l = Tg (i1.toNat + l)) :
    Native.Fill Tg (fun k ↦ (i0.toNat ≤ k ∧ k < i0.toNat + 8) ∨ (i1.toNat ≤ k ∧ k < i1.toNat + 8))
      N (rows2 v i0 i1) := by
  have f0 := Native.fill_storeWords8 Tg N (i0 * 4) _ (v 0) (Native.wordOffset_toNat' _ (by omega))
    hN h0 hv0
  have f1 := Native.fill_storeWords8 Tg N (i1 * 4) _ (v 1) (Native.wordOffset_toNat' _ (by omega))
    hN h1 hv1
  exact (f0.comp f1).congr fun b ↦ by simp only [Function.comp_apply, rows2]

/-- The values a scaled first radix-four row stores: quarter `c`, lane `l`. -/
def scaledQuadValues (th tl T C : Array (FastField p)) (q k R : USize) (c l : Nat) : UInt32 :=
  let t (c' : Nat) : USize := match c' with
    | 0 => k | 1 => k + q | 2 => k + 2 * q | _ => k + 3 * q
  let s (c' : Nat) : USize := match c' with
    | 0 => R | 1 => R + 16 | 2 => R + 8 | _ => R + 24
  let x (c' : Nat) : FastField p := T.getD ((t c').toNat + (0 : USize).toNat) 0 *
    C.getD ((s c').toNat + (OfNat.ofNat l : USize).toNat) 0
  let y := quadOutputs (th.getD (k.toNat + (0 : USize).toNat) 0)
    (th.getD ((k + q).toNat + (0 : USize).toNat) 0) (tl.getD (k.toNat + (0 : USize).toNat) 0)
    (x 0) (x 1) (x 2) (x 3)
  match c with
  | 0 => y.1.val | 1 => y.2.1.val | 2 => y.2.2.1.val | _ => y.2.2.2.val

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- A scaled first radix-four row whose words fit stores its four rows. -/
theorem Native.stripScaledQuadCell_eq (th tl T C : Array (FastField p)) (q k : USize)
    (sh : UInt32) (out : ByteArray) (h)
    (hs : 4 * ((8 * (reverse32 k.toUInt32 >>> sh).toUSize).toNat + 32) ≤ (encode C).size) :
    Native.stripScaledQuadCell p (encode th) (encode tl) (encode T) (encode C) q sh k out h =
      rows4 (scaledQuadValues th tl T C q k (8 * (reverse32 k.toUInt32 >>> sh).toUSize))
        (8 * k) (8 * (k + q)) (8 * (k + 2 * q)) (8 * (k + 3 * q)) out := by
  unfold Native.stripScaledQuadCell
  rw [dite_eq_left_of_eq_true (eq_true hs)]
  unfold Native.stripScaledQuad
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ h.2.1, Native.touchLast, Native.touch_eq,
    Native.readUOffset_encode, add_val, sub_val, mul_val]
  rfl

/-- A shifted thirty-two-bit reversal of a machine index below `2 ^ m`. -/
theorem reverse32_usize (m k : Nat) (hm : 0 < m) (h32 : m ≤ 32) (hk : k < 2 ^ m) :
    (reverse32 k.toUSize.toUInt32 >>> (32 - m).toUInt32).toNat = NTT.Transform.bitRevNat m k := by
  have hk32 : k < 2 ^ 32 := lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) h32)
  have he : k.toUSize.toUInt32 = k.toUInt32 := by
    apply UInt32.toNat_inj.mp
    rw [USize.toNat_toUInt32, USize.toNat_ofNat_of_lt' (lt_of_lt_of_le hk32 USize.le_size),
      Nat.mod_eq_of_lt hk32, Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hk32]
  rw [he]
  exact NTTFast.reverse32_shift_eq_bitRevNat m k hm h32

/-- The source row of a scaled first radix-four row, in words. -/
theorem scaled_source (m k : Nat) (hm : 0 < m) (h32 : m ≤ 32) (hk : k < 2 ^ m)
    (hu : 8 * 2 ^ m < USize.size) :
    (8 * (reverse32 k.toUSize.toUInt32 >>> (32 - m).toUInt32).toUSize).toNat =
      8 * NTT.Transform.bitRevNat m k := by
  have hb := NTT.Transform.bitRevNat_lt m k
  rw [Native.usize_mul_toNat 8 _ (by decide) (by
      rw [UInt32.toNat_toUSize, reverse32_usize m k hm h32 hk]; omega),
    UInt32.toNat_toUSize, reverse32_usize m k hm h32 hk]

/-- The reversal of a row `k + c 2 ^ (m - 2)` of the first radix-four pass. -/
theorem bitRev_quarter (m k c : Nat) (hm : 2 ≤ m) (hk : k < 2 ^ (m - 2)) :
    NTT.Transform.bitRevNat m (c * 2 ^ (m - 2) + k) =
      4 * NTT.Transform.bitRevNat (m - 2) k + NTT.Transform.bitRevNat 2 c := by
  have h := bitRevNat_concat 2 (m - 2) c k hk
  rw [show 2 + (m - 2) = m by omega] at h
  rw [Nat.mul_comm c, h]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **A scaled first radix-four row stores the first pass of the coset product.** -/
theorem scaledQuadValues_eq (tw : Array (Array (FastField p))) (m : Nat) (hm2 : 2 ≤ m)
    (hm : m % 2 = 0) (h32 : m ≤ 32) (T C : Array (FastField p)) (hT : T.size = 2 ^ m)
    (hu : 4 * (8 * 2 ^ m) < USize.size) (k : Nat)
    (hk : k < 2 ^ (m - 2)) (c : Nat) (hc : c < 4) (l : Nat) (hl : l < 8) :
    scaledQuadValues (tw.getD (m - 1) #[]) (tw.getD (m - 2) #[]) T C (2 ^ (m - 2)).toUSize
      k.toUSize (8 * (reverse32 k.toUSize.toUInt32 >>> (32 - m).toUInt32).toUSize) c l =
      ((firstLayers tw m (scaledRows T C m)).getD (8 * (k + c * 2 ^ (m - 2)) + l) 0).val := by
  have h4 : 4 * 2 ^ (m - 2) = 2 ^ m := by
    rw [show 4 = 2 ^ 2 by rfl, ← Nat.pow_add]; congr 1; omega
  set q := 2 ^ (m - 2) with hqd
  have hqU : q.toUSize.toNat = q := USize.toNat_ofNat_of_lt' (by omega)
  have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  have hkm : k < 2 ^ m := by omega
  have hR := scaled_source m k (by omega) h32 hkm (by omega)
  have hrk : NTT.Transform.bitRevNat m k = 4 * NTT.Transform.bitRevNat (m - 2) k := by
    have := bitRev_quarter m k 0 hm2 hk
    rw [Nat.zero_mul, Nat.zero_add] at this
    rw [this]
    rfl
  set r := NTT.Transform.bitRevNat (m - 2) k with hrd
  have hr : r < q := NTT.Transform.bitRevNat_lt _ _
  set R := 8 * (reverse32 k.toUSize.toUInt32 >>> (32 - m).toUInt32).toUSize with hRd
  have hRo (o : Nat) (ho : o ≤ 24) : (R + OfNat.ofNat o).toNat = 32 * r + o := by
    rw [Native.usize_add_toNat _ _ (by rw [Native.usize_numeral o (by omega), hR, hrk]; omega),
      Native.usize_numeral o (by omega), hR, hrk]
    ring
  have htc (c' : Nat) (hc' : c' < 4) :
      (k.toUSize + OfNat.ofNat c' * q.toUSize).toNat = k + c' * q := by
    have : c' * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
    rw [Native.usize_add_mul_numeral _ _ c' (by omega) (by rw [hkU, hqU]; omega), hkU, hqU]
  -- The target.
  have hX : (scaledRows T C m).size = 8 * 2 ^ m := by simp only [scaledRows, Array.size_ofFn]
  unfold firstLayers
  rw [ite_eq_right (by omega), getD_butterflyDIFRadix4Blocks _ _ _ 1 (by omega) 0 _
    (by rw [hX]; omega)]
  have hcq : c * (8 * q) + (8 * k + l) < 4 * (8 * q) := by
    have : c * (8 * q) ≤ 3 * (8 * q) := Nat.mul_le_mul_right _ (by omega)
    omega
  have ei : 8 * (k + c * q) + l = 0 * (4 * (8 * q)) + (c * (8 * q) + (8 * k + l)) := by ring
  rw [← hqd, ei, ite_eq_left ⟨by omega, by omega⟩]
  obtain ⟨g1, g2, g3⟩ := quadPass_coords (8 * q) 0 c (8 * k + l) (by omega) hc (by omega)
  simp only [Nat.zero_mul, Nat.zero_add] at g1 g2 g3
  unfold quadPassValue
  simp only [Nat.zero_mul, Nat.zero_add]
  simp only [g1, g2, g3, Nat.zero_mul, Nat.zero_add, getD_expand8]
  have hxr (c' : Nat) (hc' : c' < 4) : (scaledRows T C m).getD (c' * (8 * q) + (8 * k + l)) 0 =
      T.getD (k + c' * q) 0 * C.getD (32 * r + 8 * NTT.Transform.bitRevNat 2 c' + l) 0 := by
    have : c' * (8 * q) ≤ 3 * (8 * q) := Nat.mul_le_mul_right _ (by omega)
    have e8 : c' * (8 * q) = 8 * (c' * q) := by ring
    rw [scaledRows, getD_ofFn_bounded _ _ (by omega)]
    have d1 : (c' * (8 * q) + (8 * k + l)) / 8 = c' * q + k := by omega
    have d2 : (c' * (8 * q) + (8 * k + l)) % 8 = l := by omega
    simp only [d1, d2]
    rw [bitRev_quarter m k c' hm2 hk, Nat.add_comm (c' * q)]
    congr 2
    ring
  have hx0 := hxr 0 (by decide)
  simp only [Nat.zero_mul, Nat.zero_add] at hx0
  rw [hx0, hxr 1 (by decide), hxr 2 (by decide), hxr 3 (by decide)]
  have t1 : (8 * k + l) / 8 = k := by omega
  have t2 : (8 * k + l + 8 * q) / 8 = k + q := by omega
  rw [t1, t2]
  unfold scaledQuadValues
  simp only [USize.toNat_zero, Nat.add_zero, hkU, Native.usize_numeral l (by omega)]
  rw [Native.usize_add_toNat _ _ (by rw [hkU, hqU]; omega), hkU, hqU,
    hRo 16 (by decide), hRo 8 (by decide), hRo 24 (by decide),
    show R.toNat = 32 * r + 0 by rw [hR, hrk]; ring]
  have b0 : NTT.Transform.bitRevNat 2 0 = 0 := rfl
  have b1 : NTT.Transform.bitRevNat 2 1 = 2 := rfl
  have b2 : NTT.Transform.bitRevNat 2 2 = 1 := rfl
  have b3 : NTT.Transform.bitRevNat 2 3 = 3 := rfl
  rw [b0, b1, b2, b3]
  have e1 := htc 1 (by decide)
  have e2 := htc 2 (by decide)
  have e3 := htc 3 (by decide)
  rw [Nat.one_mul] at e1
  rw [e2, e3]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.one_mul, Nat.reduceMul]
  interval_cases c <;> rfl

/-- The values a scaled first radix-two row stores: half `c`, lane `l`. -/
def scaledPairValues (tw T C : Array (FastField p)) (q k R : USize) (c l : Nat) : UInt32 :=
  let x0 : FastField p := T.getD (k.toNat + (0 : USize).toNat) 0 *
    C.getD (R.toNat + (OfNat.ofNat l : USize).toNat) 0
  let x1 : FastField p := T.getD ((k + q).toNat + (0 : USize).toNat) 0 *
    C.getD ((R + 8).toNat + (OfNat.ofNat l : USize).toNat) 0
  match c with
  | 0 => (x0 + x1).val
  | _ => (tw.getD (k.toNat + (0 : USize).toNat) 0 * (x0 - x1)).val

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- A scaled first radix-two row whose words fit stores its two rows. -/
theorem Native.stripScaledPairCell_eq (tw T C : Array (FastField p)) (q k : USize)
    (sh : UInt32) (out : ByteArray) (h)
    (hs : 4 * ((8 * (reverse32 k.toUInt32 >>> sh).toUSize).toNat + 16) ≤ (encode C).size) :
    Native.stripScaledPairCell p (encode tw) (encode T) (encode C) q sh k out h =
      rows2 (scaledPairValues tw T C q k (8 * (reverse32 k.toUInt32 >>> sh).toUSize))
        (8 * k) (8 * (k + q)) out := by
  unfold Native.stripScaledPairCell
  rw [dite_eq_left_of_eq_true (eq_true hs)]
  unfold Native.stripScaledPair
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ h.2.1, Native.touchLast, Native.touch_eq,
    Native.readUOffset_encode, add_val, sub_val, mul_val]
  rfl

/-- The reversal of a row `k + c 2 ^ (m - 1)` of the first radix-two layer. -/
theorem bitRev_half (m k c : Nat) (hm : 1 ≤ m) (hk : k < 2 ^ (m - 1)) :
    NTT.Transform.bitRevNat m (c * 2 ^ (m - 1) + k) =
      2 * NTT.Transform.bitRevNat (m - 1) k + NTT.Transform.bitRevNat 1 c := by
  have h := bitRevNat_concat 1 (m - 1) c k hk
  rw [show 1 + (m - 1) = m by omega] at h
  rw [Nat.mul_comm c, h]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- **A scaled first radix-two row stores the first layer of the coset product.** -/
theorem scaledPairValues_eq (tw : Array (Array (FastField p))) (m : Nat) (hm1 : 1 ≤ m)
    (hm : m % 2 = 1) (h32 : m ≤ 32) (T C : Array (FastField p)) (hT : T.size = 2 ^ m)
    (hu : 4 * (8 * 2 ^ m) < USize.size) (k : Nat)
    (hk : k < 2 ^ (m - 1)) (c : Nat) (hc : c < 2) (l : Nat) (hl : l < 8) :
    scaledPairValues (tw.getD (m - 1) #[]) T C (2 ^ (m - 1)).toUSize k.toUSize
      (8 * (reverse32 k.toUSize.toUInt32 >>> (32 - m).toUInt32).toUSize) c l =
      ((firstLayers tw m (scaledRows T C m)).getD (8 * (k + c * 2 ^ (m - 1)) + l) 0).val := by
  have h2 : 2 * 2 ^ (m - 1) = 2 ^ m := by rw [← Nat.pow_succ']; congr 1; omega
  set q := 2 ^ (m - 1) with hqd
  have hqU : q.toUSize.toNat = q := USize.toNat_ofNat_of_lt' (by omega)
  have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  have hkm : k < 2 ^ m := by omega
  have hR := scaled_source m k (by omega) h32 hkm (by omega)
  have hrk : NTT.Transform.bitRevNat m k = 2 * NTT.Transform.bitRevNat (m - 1) k := by
    have := bitRev_half m k 0 hm1 hk
    rw [Nat.zero_mul, Nat.zero_add] at this
    rw [this]
    rfl
  set r := NTT.Transform.bitRevNat (m - 1) k with hrd
  have hr : r < q := NTT.Transform.bitRevNat_lt _ _
  set R := 8 * (reverse32 k.toUSize.toUInt32 >>> (32 - m).toUInt32).toUSize with hRd
  have hR8 : (R + 8).toNat = 16 * r + 8 := by
    rw [Native.usize_add_toNat _ _ (by rw [Native.usize_numeral 8 (by decide), hR, hrk]; omega),
      Native.usize_numeral 8 (by decide), hR, hrk]
    ring
  have hX : (scaledRows T C m).size = 8 * 2 ^ m := by simp only [scaledRows, Array.size_ofFn]
  have hxr (c' : Nat) (hc' : c' < 2) : (scaledRows T C m).getD (c' * (8 * q) + (8 * k + l)) 0 =
      T.getD (k + c' * q) 0 * C.getD (16 * r + 8 * c' + l) 0 := by
    have : c' * (8 * q) ≤ 1 * (8 * q) := Nat.mul_le_mul_right _ (by omega)
    have e8 : c' * (8 * q) = 8 * (c' * q) := by ring
    rw [scaledRows, getD_ofFn_bounded _ _ (by omega)]
    have d1 : (c' * (8 * q) + (8 * k + l)) / 8 = c' * q + k := by omega
    have d2 : (c' * (8 * q) + (8 * k + l)) % 8 = l := by omega
    simp only [d1, d2]
    rw [bitRev_half m k c' hm1 hk, Nat.add_comm (c' * q)]
    have hb1 : NTT.Transform.bitRevNat 1 c' = c' := by interval_cases c' <;> rfl
    rw [hb1]
    congr 2
    ring
  have hx0 := hxr 0 (by decide)
  have hx1 := hxr 1 (by decide)
  simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    at hx0 hx1
  unfold firstLayers scaledPairValues
  rw [ite_eq_left hm, ← hqd, getD_butterflyDIFInner _ _ _ _ _ _ (by rw [hX]; omega) (by omega)]
  simp only [USize.toNat_zero, Nat.add_zero, hkU, Native.usize_numeral l (by omega), hR8,
    show R.toNat = 16 * r by rw [hR, hrk]; ring,
    Native.usize_add_toNat _ _ (show k.toUSize.toNat + q.toUSize.toNat < USize.size by
      rw [hkU, hqU]; omega), hqU]
  unfold difValue
  interval_cases c
  · rw [ite_eq_left ⟨by omega, by omega⟩]
    simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero]
    rw [hx0, hx1]
  · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]
    have e1 : 8 * (k + 1 * q) + l - 8 * q = 8 * k + l := by omega
    have e2 : 8 * (k + 1 * q) + l = 8 * q + (8 * k + l) := by ring
    rw [e1, e2, Nat.zero_add, hx0, hx1, getD_expand8, div8_add _ _ hl]
    rfl

/-- The scaled radix-two row loop depends only on its arguments' values. -/
theorem Native.stripScaledPairRows_congr {tw T src : ByteArray} {q q' : USize} {sh : UInt32}
    {n : Nat} {k k' : USize} {out : ByteArray} (h) (eq : q = q') (ek : k = k') :
    Native.stripScaledPairRows p tw T src q sh n k out h =
      Native.stripScaledPairRows p tw T src q' sh n k' out (eq ▸ ek ▸ h) := by
  subst eq ek
  rfl

/-- The scaled radix-four row loop depends only on its arguments' values. -/
theorem Native.stripScaledQuadRows_congr {th tl T src : ByteArray} {q q' : USize} {sh : UInt32}
    {n : Nat} {k k' : USize} {out : ByteArray} (h) (eq : q = q') (ek : k = k') :
    Native.stripScaledQuadRows p th tl T src q sh n k out h =
      Native.stripScaledQuadRows p th tl T src q' sh n k' out (eq ▸ ek ▸ h) := by
  subst eq ek
  rfl

/-- **The scaled first layers on packed words** are the first layers of the coset product. -/
theorem Native.stripScaled_encode (tw : Array (Array (FastField p))) (m : Nat) (hm : 1 ≤ m)
    (h32 : m ≤ 32) (htw : TwiddleSizes m tw) (T C : Array (FastField p)) (hT : T.size = 2 ^ m)
    (hC : C.size = 8 * 2 ^ m) (hu : 4 * (8 * 2 ^ m) < USize.size) :
    Native.stripScaled p (tw.map encode) (encode T) (encode C) m =
      encode (firstLayers tw m (scaledRows T C m)) := by
  let Tg (i : Nat) : UInt32 := ((firstLayers tw m (scaledRows T C m)).getD i 0).val
  let N := 8 * 2 ^ m
  have hN : 4 * N < USize.size := hu
  have hsz : (firstLayers tw m (scaledRows T C m)).size = N := by
    unfold firstLayers
    split <;> simp only [Plan.size_butterflyDIFInner, Plan.size_butterflyDIFRadix4Blocks,
      scaledRows, Array.size_ofFn, N]
  have hfin (S : Nat → Prop) (g : ByteArray → ByteArray) (hf : Native.Fill Tg S N g)
      (hS : ∀ i < N, S i) : g (zeroWords (8 * 2 ^ m)) =
        encode (firstLayers tw m (scaledRows T C m)) := by
    rw [Native.zeroWords_eq, hf.eq_ofFn hS _ Array.size_replicate, encode_eq_map_val]
    congr 1
    apply Array.ext (by rw [Array.size_ofFn, Array.size_map, hsz])
    intro i h1 h2
    simp only [Array.getElem_ofFn, Array.getElem_map, Tg]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by
      rw [hsz]; rw [Array.size_ofFn] at h1; exact h1), Option.getD_some]
  have hTs : (encode T).size = 4 * 2 ^ m := by rw [size_encode_fields, hT]
  have hCs : (encode C).size = 4 * (8 * 2 ^ m) := by rw [size_encode_fields, hC]
  unfold Native.stripScaled
  dsimp only
  simp only [getD_map_encode]
  split
  · rename_i hodd
    set q := 2 ^ (m - 1) with hqd
    have h2 : 2 * q = 2 ^ m := by rw [hqd, ← Nat.pow_succ']; congr 1; omega
    have hqU : q.toUSize.toNat = q := USize.toNat_ofNat_of_lt' (by omega)
    have htws : (encode (tw.getD (m - 1) #[])).size = 4 * q := by
      rw [size_encode_fields, htw _ (by omega)]
    let tw1 := encode (tw.getD (m - 1) #[])
    have hcell (k : Nat) (hk : k < q) :
        Native.Fill Tg (fun i ↦ (8 * k ≤ i ∧ i < 8 * k + 8) ∨
          (8 * (k + q) ≤ i ∧ i < 8 * (k + q) + 8)) N (fun out ↦
          if h : Native.ScaledPairFits tw1 (encode T) (encode C) out q.toUSize k.toUSize then
            Native.stripScaledPairCell p tw1 (encode T) (encode C) q.toUSize (32 - m).toUInt32
              k.toUSize out h
          else out) := by
      have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
      have hkq : (k.toUSize + q.toUSize).toNat = k + q := by
        rw [Native.usize_add_toNat _ _ (by rw [hkU, hqU]; omega), hkU, hqU]
      have hr0 : (8 * k.toUSize).toNat = 8 * k := by
        rw [Native.usize_mul_toNat 8 _ (by decide) (by rw [hkU]; omega), hkU]
      have hr1 : (8 * (k.toUSize + q.toUSize)).toNat = 8 * (k + q) := by
        rw [Native.usize_mul_toNat 8 _ (by decide) (by rw [hkq]; omega), hkq]
      have hR := scaled_source m k (by omega) h32 (by omega) (by omega)
      have hb := NTT.Transform.bitRevNat_lt m k
      have hrk : NTT.Transform.bitRevNat m k = 2 * NTT.Transform.bitRevNat (m - 1) k := by
        have := bitRev_half m k 0 hm (by omega)
        rw [Nat.zero_mul, Nat.zero_add] at this
        rw [this]
        rfl
      have hr' := NTT.Transform.bitRevNat_lt (m - 1) k
      have hf := Native.fill_rows2 Tg N hN (scaledPairValues (tw.getD (m - 1) #[]) T C q.toUSize
        k.toUSize (8 * (reverse32 k.toUSize.toUInt32 >>> (32 - m).toUInt32).toUSize))
        (8 * k.toUSize) (8 * (k.toUSize + q.toUSize)) (by rw [hr0]; omega)
        (by rw [hr1]; omega)
        (fun l hl ↦ by
          rw [hr0, scaledPairValues_eq tw m hm hodd h32 T C hT hu k hk 0 (by decide) l hl]
          simp only [Tg, Nat.zero_mul, Nat.add_zero])
        (fun l hl ↦ by
          rw [hr1, scaledPairValues_eq tw m hm hodd h32 T C hT hu k hk 1 (by decide) l hl]
          simp only [Tg, Nat.one_mul, ← hqd])
      refine (hf.congr_encode fun o ho ↦ ?_).mono ?_
      · have hfit : Native.ScaledPairFits tw1 (encode T) (encode C) (encode o) q.toUSize
            k.toUSize := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [size_encode_uint32, ho, hkU, hqU, hCs, hTs, htws, N, tw1] <;> omega
        rw [dite_eq_left_of_eq_true (eq_true hfit)]
        exact (Native.stripScaledPairCell_eq _ T C _ _ _ _ hfit (by
          rw [hCs, hR, hrk]; omega)).symm
      · intro i hi
        simpa only [hr0, hr1] using hi
    let H (n : Nat) (k : USize) (out : ByteArray) : Prop :=
      4 * (8 * (k.toNat + q.toUSize.toNat + n)) ≤ out.size ∧ out.size < USize.size ∧
        (encode C).size < USize.size ∧ 4 * (k.toNat + q.toUSize.toNat + n) ≤ (encode T).size ∧
        (encode T).size < USize.size ∧ 4 * (k.toNat + n) ≤ tw1.size ∧ tw1.size < USize.size
    have hloop : ∀ n k, k + n ≤ q → Native.Fill Tg (fun i ↦ ∃ j, k ≤ j ∧ j < k + n ∧
        ((8 * j ≤ i ∧ i < 8 * j + 8) ∨ (8 * (j + q) ≤ i ∧ i < 8 * (j + q) + 8))) N
        (fun out ↦ if h : H n k.toUSize out then Native.stripScaledPairRows p tw1 (encode T)
          (encode C) q.toUSize (32 - m).toUInt32 n k.toUSize out h else out) := by
      intro n
      induction n with
      | zero =>
        intro k _
        refine ((Native.Fill.id Tg N).congr fun b ↦ ?_).mono fun i ⟨j, h1, h2, _⟩ ↦ by omega
        split <;> rfl
      | succ n ih =>
        intro k hk
        have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
        have hk1 : k.toUSize + 1 = (k + 1).toUSize := by
          apply USize.toNat_inj.mp
          rw [Native.usize_add_toNat _ _ (by rw [hkU, Native.usize_numeral 1 (by decide)]; omega),
            hkU, Native.usize_numeral 1 (by decide), USize.toNat_ofNat_of_lt' (by omega)]
        refine (((hcell k (by omega)).comp (ih (k + 1) (by omega))).congr_encode
          fun o ho ↦ ?_).mono ?_
        · have hA : H (n + 1) k.toUSize (encode o) := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [size_encode_uint32, ho, hkU, hqU, hCs, hTs, htws, N, tw1] <;> omega
          have hfit : Native.ScaledPairFits tw1 (encode T) (encode C) (encode o) q.toUSize
              k.toUSize := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [size_encode_uint32, ho, hkU, hqU, hCs, hTs, htws, N, tw1] <;> omega
          have hB : H n (k + 1).toUSize (Native.stripScaledPairCell p tw1 (encode T) (encode C)
              q.toUSize (32 - m).toUInt32 k.toUSize (encode o) hfit) := by
            have hk1N : (k + 1).toUSize.toNat = k + 1 := USize.toNat_ofNat_of_lt' (by omega)
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [Native.size_stripScaledPairCell, size_encode_uint32, ho, hqU, hCs, hTs,
                htws, hk1N, tw1] <;> omega
          simp only [Function.comp_apply]
          rw [dite_eq_left_of_eq_true (eq_true hfit), dite_eq_left_of_eq_true (eq_true hB),
            dite_eq_left_of_eq_true (eq_true hA), Native.stripScaledPairRows]
          exact (Native.stripScaledPairRows_congr _ rfl hk1).symm
        · rintro i ⟨j, h1, h2, h3⟩
          by_cases hj : j = k
          · subst hj; exact Or.inl h3
          · exact Or.inr ⟨j, by omega, by omega, h3⟩
    have hl0 := hloop q 0 (by omega)
    have hA0 : H q (0 : Nat).toUSize (zeroWords (8 * 2 ^ m)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Native.zeroWords_eq, size_encode_uint32, Array.size_replicate,
          show (0 : Nat).toUSize.toNat = 0 from rfl, hqU, hCs, hTs, htws, tw1] <;> omega
    have hcover : ∀ i < N, ∃ j, 0 ≤ j ∧ j < 0 + q ∧
        ((8 * j ≤ i ∧ i < 8 * j + 8) ∨ (8 * (j + q) ≤ i ∧ i < 8 * (j + q) + 8)) := by
      intro i hi
      obtain ⟨j, l, hl, rfl⟩ : ∃ j l, l < 8 ∧ i = 8 * j + l :=
        ⟨i / 8, i % 8, Nat.mod_lt _ (by decide), by omega⟩
      by_cases hj : j < q
      · exact ⟨j, by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩
      · exact ⟨j - q, by omega, by simp only [N] at hi; omega,
          Or.inr ⟨by omega, by omega⟩⟩
    have hfin' := hfin _ _ hl0 hcover
    rw [dite_eq_left_of_eq_true (eq_true hA0)] at hfin'
    rw [dite_eq_left_of_eq_true (eq_true (by
      simp only [Native.zeroWords_eq, size_encode_uint32, Array.size_replicate, hCs, hTs, htws]
      omega))]
    refine Eq.trans ?_ hfin'
    exact Native.stripScaledPairRows_congr _ (USize.toNat_inj.mp (by
      rw [USize.toNat_ofNatLT, hqU])) rfl
  · rename_i heven
    have hm2 : 2 ≤ m := by omega
    set q := 2 ^ (m - 2) with hqd
    have h4 : 4 * q = 2 ^ m := by
      rw [hqd, show 4 = 2 ^ 2 by rfl, ← Nat.pow_add]; congr 1; omega
    have hqU : q.toUSize.toNat = q := USize.toNat_ofNat_of_lt' (by omega)
    have h2q : 2 ^ (m - 1) = 2 * q := by
      rw [hqd, ← Nat.pow_succ']; congr 1; omega
    have hths : (encode (tw.getD (m - 1) #[])).size = 4 * (2 * q) := by
      rw [size_encode_fields, htw _ (by omega), h2q]
    have htls : (encode (tw.getD (m - 2) #[])).size = 4 * q := by
      rw [size_encode_fields, htw _ (by omega)]
    let th1 := encode (tw.getD (m - 1) #[])
    let tl1 := encode (tw.getD (m - 2) #[])
    have hcell (k : Nat) (hk : k < q) :
        Native.Fill Tg (fun i ↦ ((8 * k ≤ i ∧ i < 8 * k + 8) ∨
          (8 * (k + q) ≤ i ∧ i < 8 * (k + q) + 8)) ∨ (8 * (k + 2 * q) ≤ i ∧
            i < 8 * (k + 2 * q) + 8) ∨ (8 * (k + 3 * q) ≤ i ∧ i < 8 * (k + 3 * q) + 8)) N
          (fun out ↦ if h : Native.ScaledQuadFits th1 tl1 (encode T) (encode C) out q.toUSize
              k.toUSize then
            Native.stripScaledQuadCell p th1 tl1 (encode T) (encode C) q.toUSize
              (32 - m).toUInt32 k.toUSize out h
          else out) := by
      have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
      have hkc (c : Nat) (hc : c < 4) :
          (k.toUSize + OfNat.ofNat c * q.toUSize).toNat = k + c * q := by
        have : c * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
        rw [Native.usize_add_mul_numeral _ _ c (by omega) (by rw [hkU, hqU]; omega), hkU, hqU]
      have hkq : (k.toUSize + q.toUSize).toNat = k + q := by
        rw [Native.usize_add_toNat _ _ (by rw [hkU, hqU]; omega), hkU, hqU]
      have hrow (x : USize) (n : Nat) (hx : x.toNat = n) (hn : n < 4 * q) :
          (8 * x).toNat = 8 * n := by
        rw [Native.usize_mul_toNat 8 _ (by decide) (by rw [hx]; omega), hx]
      have hr0 := hrow _ _ hkU (by omega)
      have hr1 := hrow _ _ hkq (by omega)
      have hr2 := hrow _ _ (hkc 2 (by decide)) (by omega)
      have hr3 := hrow _ _ (hkc 3 (by decide)) (by omega)
      have hR := scaled_source m k (by omega) h32 (by omega) (by omega)
      have hrk : NTT.Transform.bitRevNat m k = 4 * NTT.Transform.bitRevNat (m - 2) k := by
        have := bitRev_quarter m k 0 hm2 (by omega)
        rw [Nat.zero_mul, Nat.zero_add] at this
        rw [this]
        rfl
      have hr' := NTT.Transform.bitRevNat_lt (m - 2) k
      have hv (c : Nat) (hc : c < 4) (l : Nat) (hl : l < 8) :=
        scaledQuadValues_eq tw m hm2 (by omega) h32 T C hT hu k hk c hc l hl
      have hf := Native.fill_rows4 Tg N hN (scaledQuadValues (tw.getD (m - 1) #[])
        (tw.getD (m - 2) #[]) T C q.toUSize k.toUSize
        (8 * (reverse32 k.toUSize.toUInt32 >>> (32 - m).toUInt32).toUSize))
        (8 * k.toUSize) (8 * (k.toUSize + q.toUSize)) (8 * (k.toUSize + 2 * q.toUSize))
        (8 * (k.toUSize + 3 * q.toUSize)) (by rw [hr0]; omega) (by rw [hr1]; omega)
        (by rw [hr2]; omega) (by rw [hr3]; omega)
        (fun l hl ↦ by
          rw [hr0, hv 0 (by decide) l hl]; simp only [Tg, Nat.zero_mul, Nat.add_zero])
        (fun l hl ↦ by rw [hr1, hv 1 (by decide) l hl]; simp only [Tg, Nat.one_mul, ← hqd])
        (fun l hl ↦ by rw [hr2, hv 2 (by decide) l hl])
        (fun l hl ↦ by rw [hr3, hv 3 (by decide) l hl])
      refine (hf.congr_encode fun o ho ↦ ?_).mono ?_
      · have hfit : Native.ScaledQuadFits th1 tl1 (encode T) (encode C) (encode o) q.toUSize
            k.toUSize := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [size_encode_uint32, ho, hkU, hqU, hCs, hTs, hths, htls, N, th1, tl1] <;>
            omega
        rw [dite_eq_left_of_eq_true (eq_true hfit)]
        exact (Native.stripScaledQuadCell_eq _ _ T C _ _ _ _ hfit (by
          rw [hCs, hR, hrk]; omega)).symm
      · intro i hi
        simpa only [hr0, hr1, hr2, hr3] using hi
    let H (n : Nat) (k : USize) (out : ByteArray) : Prop :=
      4 * (8 * (k.toNat + 3 * q.toUSize.toNat + n)) ≤ out.size ∧ out.size < USize.size ∧
        (encode C).size < USize.size ∧ 4 * (k.toNat + 3 * q.toUSize.toNat + n) ≤ (encode T).size ∧
        (encode T).size < USize.size ∧ 4 * (k.toNat + q.toUSize.toNat + n) ≤ th1.size ∧
        th1.size < USize.size ∧ 4 * (k.toNat + n) ≤ tl1.size ∧ tl1.size < USize.size
    have hloop : ∀ n k, k + n ≤ q → Native.Fill Tg (fun i ↦ ∃ j, k ≤ j ∧ j < k + n ∧
        (((8 * j ≤ i ∧ i < 8 * j + 8) ∨ (8 * (j + q) ≤ i ∧ i < 8 * (j + q) + 8)) ∨
          (8 * (j + 2 * q) ≤ i ∧ i < 8 * (j + 2 * q) + 8) ∨
          (8 * (j + 3 * q) ≤ i ∧ i < 8 * (j + 3 * q) + 8))) N
        (fun out ↦ if h : H n k.toUSize out then Native.stripScaledQuadRows p th1 tl1 (encode T)
          (encode C) q.toUSize (32 - m).toUInt32 n k.toUSize out h else out) := by
      intro n
      induction n with
      | zero =>
        intro k _
        refine ((Native.Fill.id Tg N).congr fun b ↦ ?_).mono fun i ⟨j, h1, h2, _⟩ ↦ by omega
        split <;> rfl
      | succ n ih =>
        intro k hk
        have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
        have hk1 : k.toUSize + 1 = (k + 1).toUSize := by
          apply USize.toNat_inj.mp
          rw [Native.usize_add_toNat _ _ (by rw [hkU, Native.usize_numeral 1 (by decide)]; omega),
            hkU, Native.usize_numeral 1 (by decide), USize.toNat_ofNat_of_lt' (by omega)]
        refine (((hcell k (by omega)).comp (ih (k + 1) (by omega))).congr_encode
          fun o ho ↦ ?_).mono ?_
        · have hA : H (n + 1) k.toUSize (encode o) := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [size_encode_uint32, ho, hkU, hqU, hCs, hTs, hths, htls, N, th1, tl1] <;>
              omega
          have hfit : Native.ScaledQuadFits th1 tl1 (encode T) (encode C) (encode o) q.toUSize
              k.toUSize := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [size_encode_uint32, ho, hkU, hqU, hCs, hTs, hths, htls, N, th1, tl1] <;>
              omega
          have hB : H n (k + 1).toUSize (Native.stripScaledQuadCell p th1 tl1 (encode T)
              (encode C) q.toUSize (32 - m).toUInt32 k.toUSize (encode o) hfit) := by
            have hk1N : (k + 1).toUSize.toNat = k + 1 := USize.toNat_ofNat_of_lt' (by omega)
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [Native.size_stripScaledQuadCell, size_encode_uint32, ho, hqU, hCs, hTs,
                hths, htls, hk1N, th1, tl1] <;> omega
          simp only [Function.comp_apply]
          rw [dite_eq_left_of_eq_true (eq_true hfit), dite_eq_left_of_eq_true (eq_true hB),
            dite_eq_left_of_eq_true (eq_true hA), Native.stripScaledQuadRows]
          exact (Native.stripScaledQuadRows_congr _ rfl hk1).symm
        · rintro i ⟨j, h1, h2, h3⟩
          by_cases hj : j = k
          · subst hj; exact Or.inl h3
          · exact Or.inr ⟨j, by omega, by omega, h3⟩
    have hl0 := hloop q 0 (by omega)
    have hA0 : H q (0 : Nat).toUSize (zeroWords (8 * 2 ^ m)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Native.zeroWords_eq, size_encode_uint32, Array.size_replicate,
          show (0 : Nat).toUSize.toNat = 0 from rfl, hqU, hCs, hTs, hths, htls, th1, tl1] <;>
        omega
    have hcover : ∀ i < N, ∃ j, 0 ≤ j ∧ j < 0 + q ∧
        (((8 * j ≤ i ∧ i < 8 * j + 8) ∨ (8 * (j + q) ≤ i ∧ i < 8 * (j + q) + 8)) ∨
          (8 * (j + 2 * q) ≤ i ∧ i < 8 * (j + 2 * q) + 8) ∨
          (8 * (j + 3 * q) ≤ i ∧ i < 8 * (j + 3 * q) + 8)) := by
      intro i hi
      obtain ⟨j, l, hl, rfl⟩ : ∃ j l, l < 8 ∧ i = 8 * j + l :=
        ⟨i / 8, i % 8, Nat.mod_lt _ (by decide), by omega⟩
      have hj : j < 4 * q := by simp only [N] at hi; omega
      by_cases j0 : j < q
      · exact ⟨j, by omega, by omega, Or.inl (Or.inl ⟨by omega, by omega⟩)⟩
      · by_cases j1 : j < 2 * q
        · exact ⟨j - q, by omega, by omega, Or.inl (Or.inr ⟨by omega, by omega⟩)⟩
        · by_cases j2 : j < 3 * q
          · exact ⟨j - 2 * q, by omega, by omega, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
          · exact ⟨j - 3 * q, by omega, by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
    have hfin' := hfin _ _ hl0 hcover
    rw [dite_eq_left_of_eq_true (eq_true hA0)] at hfin'
    rw [dite_eq_left_of_eq_true (eq_true (by
      simp only [Native.zeroWords_eq, size_encode_uint32, Array.size_replicate, hCs, hTs, hths,
        htls]
      omega))]
    refine Eq.trans ?_ hfin'
    exact Native.stripScaledQuadRows_congr _ (USize.toNat_inj.mp (by
      rw [USize.toNat_ofNatLT, hqU])) rfl


/-! ### Eight-row kernels -/

/-- Eight lines `p + u ps` of eight words stored one after another. -/
def lines8 (g : Nat → Nat → UInt32) (p ps : USize) (b : ByteArray) : ByteArray :=
  let b := Native.storeWords b ((p + 0 * ps) * 4) 8 (g 0 0) (g 0 1) (g 0 2) (g 0 3)
    (g 0 4) (g 0 5) (g 0 6) (g 0 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b ((p + 1 * ps) * 4) 8 (g 1 0) (g 1 1) (g 1 2) (g 1 3)
    (g 1 4) (g 1 5) (g 1 6) (g 1 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b ((p + 2 * ps) * 4) 8 (g 2 0) (g 2 1) (g 2 2) (g 2 3)
    (g 2 4) (g 2 5) (g 2 6) (g 2 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b ((p + 3 * ps) * 4) 8 (g 3 0) (g 3 1) (g 3 2) (g 3 3)
    (g 3 4) (g 3 5) (g 3 6) (g 3 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b ((p + 4 * ps) * 4) 8 (g 4 0) (g 4 1) (g 4 2) (g 4 3)
    (g 4 4) (g 4 5) (g 4 6) (g 4 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b ((p + 5 * ps) * 4) 8 (g 5 0) (g 5 1) (g 5 2) (g 5 3)
    (g 5 4) (g 5 5) (g 5 6) (g 5 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b ((p + 6 * ps) * 4) 8 (g 6 0) (g 6 1) (g 6 2) (g 6 3)
    (g 6 4) (g 6 5) (g 6 6) (g 6 7) 0 0 0 0 0 0 0 0
  let b := Native.storeWords b ((p + 7 * ps) * 4) 8 (g 7 0) (g 7 1) (g 7 2) (g 7 3)
    (g 7 4) (g 7 5) (g 7 6) (g 7 7) 0 0 0 0 0 0 0 0
  b

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The eight-row transpose stores its eight lines one after another. -/
theorem Native.stripSplit8_eq_lines8 (Y : Array (FastField p)) (q : USize) (out : ByteArray)
    (p ps : USize) (hq : 4 * (q.toNat + 7 * 8 + 8) ≤ 4 * Y.size) (hY : 4 * Y.size < USize.size)
    (hp : 4 * (p.toNat + 7 * ps.toNat + 8) ≤ out.size) (hout : out.size < USize.size) :
    Native.stripSplit8 (encode Y) q out p ps = lines8 (fun u t ↦
      (Y.getD ((q + OfNat.ofNat t * 8).toNat + (OfNat.ofNat u : USize).toNat) 0).val) p ps out := by
  unfold Native.stripSplit8
  rw [dite_eq_left_of_eq_true (eq_true ⟨by rw [size_encode_fields]; exact hq,
    by rw [size_encode_fields]; exact hY, hp, hout⟩)]
  unfold Native.stripTranspose8
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ hout, Native.touchLast, Native.touch_eq,
    Native.readUOffset_encode]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The eight-row copy stores its eight lines one after another. -/
theorem Native.stripCopy8_eq_lines8 (M : Array (FastField p)) (q qs : USize) (out : ByteArray)
    (p : USize) (hq : 4 * (q.toNat + 7 * qs.toNat + 8) ≤ 4 * M.size)
    (hM : 4 * M.size < USize.size) (hp : 4 * (p.toNat + 7 * 8 + 8) ≤ out.size)
    (hout : out.size < USize.size) :
    Native.stripCopy8 (encode M) q qs out p = lines8 (fun t u ↦
      (M.getD ((q + OfNat.ofNat t * qs).toNat + (OfNat.ofNat u : USize).toNat) 0).val) p 8 out := by
  unfold Native.stripCopy8
  rw [dite_eq_left_of_eq_true (eq_true ⟨by rw [size_encode_fields]; exact hq,
    by rw [size_encode_fields]; exact hM, hp, hout⟩)]
  unfold Native.stripRows8
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ hout, Native.touchLast, Native.touch_eq,
    Native.readUOffset_encode]
  rfl

/-- Eight lines `p + u ps` of eight words, each stored with its targets, fill them. -/
theorem Native.fill_lines8 (T : Nat → UInt32) (N : Nat) (p ps : USize) (hN : 4 * N < USize.size)
    (hp : p.toNat + 7 * ps.toNat + 8 ≤ N) (g : Nat → Nat → UInt32)
    (hg : ∀ u < 8, ∀ t < 8, g u t = T (p.toNat + u * ps.toNat + t)) :
    Native.Fill T (fun k ↦ ∃ u < 8, ∃ t < 8, k = p.toNat + u * ps.toNat + t) N
      (lines8 g p ps) := by
  have hpu (u : Nat) (hu : u < 8) : (p + OfNat.ofNat u * ps).toNat = p.toNat + u * ps.toNat := by
    have := Nat.mul_le_mul_right ps.toNat (show u ≤ 7 by omega)
    exact Native.usize_add_mul_numeral p ps u (by omega) (by omega)
  have hstep (u : Nat) (hu : u < 8) :
      Native.Fill T (fun k ↦ p.toNat + u * ps.toNat ≤ k ∧ k < p.toNat + u * ps.toNat + 8) N
        (fun b ↦ Native.storeWords b ((p + OfNat.ofNat u * ps) * 4) 8 (g u 0) (g u 1) (g u 2)
          (g u 3) (g u 4) (g u 5) (g u 6) (g u 7) 0 0 0 0 0 0 0 0) := by
    have := Nat.mul_le_mul_right ps.toNat (show u ≤ 7 by omega)
    exact Native.fill_storeWords8 T N _ (p.toNat + u * ps.toNat) (g u)
      (by rw [Native.wordOffset_toNat' _ (by rw [hpu u hu]; omega), hpu u hu]) hN (by omega)
      (fun t ht ↦ hg u hu t ht)
  have h := (((((((hstep 0 (by decide)).comp (hstep 1 (by decide))).comp
    (hstep 2 (by decide))).comp (hstep 3 (by decide))).comp (hstep 4 (by decide))).comp
    (hstep 5 (by decide))).comp (hstep 6 (by decide))).comp (hstep 7 (by decide))
  refine (h.congr fun b ↦ ?_).mono ?_
  · simp only [Function.comp_apply, lines8]
  · rintro k ⟨u, hu, t, ht, rfl⟩
    interval_cases u <;> omega

/-- **A strip's columns on packed words** are its lanes. -/
theorem Native.stripColumns_encode (Y : Array (FastField p)) (h : Nat) (h8 : 8 ∣ h)
    (hY : Y.size = 8 * h) (hu : 4 * (8 * h) < USize.size) :
    Native.stripColumns (encode Y) h = (Array.range 8).map fun l ↦ encode (lane8 Y h l) := by
  obtain ⟨H, rfl⟩ := h8
  let T (k : Nat) : UInt32 := (Y.getD (8 * (k % (8 * H)) + k / (8 * H)) 0).val
  have hN : 4 * (8 * (8 * H)) < USize.size := hu
  have hYs : 4 * Y.size < USize.size := by omega
  have hU (n : Nat) (hn : n ≤ 8 * (8 * H)) : n.toUSize.toNat = n :=
    USize.toNat_ofNat_of_lt' (by omega)
  have htile (rb : Nat) (hrb : rb ∈ List.range' 0 (8 * H / 8)) :
      Native.Fill T (fun k ↦ ∃ u < 8, ∃ t < 8, k = 8 * rb + u * (8 * H) + t) (8 * (8 * H))
        (fun out ↦ Native.stripSplit8 (encode Y) (64 * rb).toUSize out (8 * rb).toUSize
          (8 * H).toUSize) := by
    have hrb := List.mem_range'_1.mp hrb
    have h1 : rb < H := by omega
    have hq := hU (64 * rb) (by omega)
    have hp := hU (8 * rb) (by omega)
    have hps := hU (8 * H) (by omega)
    have hf := Native.fill_lines8 T (8 * (8 * H)) (8 * rb).toUSize (8 * H).toUSize hN
      (by rw [hp, hps]; omega) (fun u t ↦ (Y.getD (((64 * rb).toUSize + OfNat.ofNat t * 8).toNat +
        (OfNat.ofNat u : USize).toNat) 0).val) (by
        intro u hu t ht
        have hqt : ((64 * rb).toUSize + OfNat.ofNat t * 8).toNat = 64 * rb + t * 8 := by
          rw [Native.usize_add_mul_numeral _ _ t (by omega) (by
            rw [hq, Native.usize_numeral 8 (by decide)]; omega), hq,
            Native.usize_numeral 8 (by decide)]
        rw [hqt, Native.usize_numeral u (by omega), hp, hps]
        simp only [T]
        have e1 : (8 * rb + u * (8 * H) + t) % (8 * H) = 8 * rb + t := by
          rw [show 8 * rb + u * (8 * H) + t = u * (8 * H) + (8 * rb + t) by ring,
            Nat.mul_add_mod_of_lt (by omega)]
        have e2 : (8 * rb + u * (8 * H) + t) / (8 * H) = u := by
          rw [show 8 * rb + u * (8 * H) + t = u * (8 * H) + (8 * rb + t) by ring,
            Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
            Nat.zero_add]
        rw [e1, e2]
        congr 2
        ring)
    refine (hf.congr_encode fun o ho ↦ ?_).mono ?_
    · rw [Native.stripSplit8_eq_lines8 Y _ _ _ _ (by rw [hq]; omega) hYs
        (by rw [size_encode_uint32, hp, hps, ho]; omega) (by rw [size_encode_uint32, ho]; omega)]
    · rintro k ⟨u, hu, t, ht, rfl⟩
      exact ⟨u, hu, t, ht, by rw [hp, hps]⟩
  have hall := Native.Fill.foldl T _ (8 * (8 * H)) _ _ htile
  unfold Native.stripColumns
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero, List.forIn_pure_yield_eq_foldl,
    Native.zeroWords_eq]
  rw [hall.eq_ofFn (fun k hk ↦ ?_) _ Array.size_replicate]
  · simp only [pure_bind, Id.run_pure]
    apply Array.ext (by simp only [Array.size_map, Array.size_range])
    intro l hl _
    simp only [Array.size_map, Array.size_range] at hl
    simp only [Array.getElem_map, Array.getElem_range]
    rw [Native.emptyWithCapacity_eq_encodeWords,
      show (0 : Nat) = (encode (#[] : Array UInt32)).size from rfl,
      show 4 * (l * (8 * H)) = PackedRepr.width UInt32 * (l * (8 * H)) from rfl,
      show 4 * (8 * H) = PackedRepr.width UInt32 * (8 * H) from rfl, PackedRepr.copySlice_encode,
      encode_eq_map_val]
    congr 1
    apply Array.ext (by
      simp only [Array.size_append, Array.size_extract, Array.size_ofFn, Array.size_map,
        size_lane8, List.size_toArray, List.length_nil]
      have : l * (8 * H) + 8 * H ≤ 8 * (8 * H) := by nlinarith
      omega)
    intro i h1 h2
    simp only [Array.size_map, size_lane8] at h2
    simp only [Array.getElem_map, Array.getElem_append_right (show (#[] : Array UInt32).size ≤ i
      from Nat.zero_le _), Array.getElem_extract, Array.getElem_ofFn, List.size_toArray,
      List.length_nil, Nat.sub_zero]
    simp only [lane8, Array.getElem_ofFn, T]
    have e1 : (l * (8 * H) + i) % (8 * H) = i := by
      rw [Nat.mul_add_mod_of_lt h2]
    have e2 : (l * (8 * H) + i) / (8 * H) = l := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h2, Nat.zero_add]
    rw [e1, e2]
  · obtain ⟨u, r, hr, rfl⟩ : ∃ u r, r < 8 * H ∧ k = u * (8 * H) + r :=
      ⟨k / (8 * H), k % (8 * H), Nat.mod_lt _ (by omega), (Nat.div_add_mod' k _).symm⟩
    have hu8 : u < 8 := by
      by_contra hc
      have : 8 * (8 * H) ≤ u * (8 * H) := Nat.mul_le_mul_right _ (by omega)
      omega
    refine ⟨r / 8, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, u, hu8, r % 8,
      Nat.mod_lt _ (by decide), by omega⟩

/-- Strip `s` of the row-major matrix `M` of width `w` with `h` rows: columns `8 s, …, 8 s + 7`
interleaved. -/
def stripOf (M : Array (FastField p)) (w s h : Nat) : Array (FastField p) :=
  Array.ofFn (n := 8 * h) fun i ↦ M.getD (i.val / 8 * w + 8 * s + i.val % 8) 0

/-- Entry `i` of a slice is entry `a + i` of the array, inside the slice. -/
theorem getD_extract_in (M : Array (FastField p)) (a b i : Nat) (hb : b ≤ M.size)
    (hi : a + i < b) : (M.extract a b).getD i 0 = M.getD (a + i) 0 := by
  have h1 : i < (M.extract a b).size := by rw [Array.size_extract]; omega
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem (show a + i < M.size by omega), Option.getD_some,
    Array.getElem_extract]

/-- **A strip gathered from row chunks** is the strip of the matrix. -/
theorem Native.stripOfChunks_rowChunks (M : Array (FastField p)) (w logH k s : Nat)
    (hk : k ≤ logH) (h8 : 8 ∣ 2 ^ (logH - k)) (hs : 8 * s + 8 ≤ w) (hM : M.size = 2 ^ logH * w)
    (hu : 4 * M.size < USize.size) (hu' : 4 * (8 * 2 ^ logH) < USize.size) :
    Native.stripOfChunks (Native.rowChunks M w logH k) w s (2 ^ (logH - k)) =
      encode (stripOf M w s (2 ^ logH)) := by
  have hpos : 0 < 2 ^ logH := Nat.two_pow_pos _
  have hR : 2 ^ k * 2 ^ (logH - k) = 2 ^ logH := by rw [← Nat.pow_add]; congr 1; omega
  set R := 2 ^ (logH - k) with hRdef
  set K := 2 ^ k with hKdef
  obtain ⟨Q, hQ⟩ := h8
  let N := 8 * (K * R)
  have hN : 4 * N < USize.size := by simp only [N]; rw [hR]; exact hu'
  let T (i : Nat) : UInt32 := (M.getD (i / 8 * w + 8 * s + i % 8) 0).val
  have hw : w ≤ M.size := by rw [hM]; exact Nat.le_mul_of_pos_left w hpos
  have hwU : w.toUSize.toNat = w := USize.toNat_ofNat_of_lt' (by omega)
  have hms : (Native.rowChunks M w logH k).size = K := by
    simp only [Native.rowChunks, Array.size_map, Array.size_range, K]
  have hKR : K * R * w = M.size := by rw [hR, hM]
  have htile (c : Nat) (hc : c ∈ List.range' 0 K) (rb : Nat) (hrb : rb ∈ List.range' 0 (R / 8)) :
      Native.Fill T (fun i ↦ ∃ t < 8, ∃ u < 8, i = 8 * (c * R + 8 * rb) + t * 8 + u) N
        (fun out ↦ Native.stripCopy8 ((Native.rowChunks M w logH k).getD c .empty)
          (8 * rb * w + 8 * s).toUSize w.toUSize out (8 * (c * R + 8 * rb)).toUSize) := by
    have hc := (List.mem_range'_1.mp hc).2
    have hrb := (List.mem_range'_1.mp hrb).2
    have hcR : (c + 1) * R ≤ K * R := Nat.mul_le_mul_right R (by omega)
    have hcRw : (c + 1) * R * w ≤ K * R * w := Nat.mul_le_mul_right w hcR
    have hrbw : (8 * rb + 8) * w ≤ R * w := Nat.mul_le_mul_right w (by omega)
    have e1 : (c + 1) * R * w = c * (R * w) + R * w := by ring
    have e2 : (8 * rb + 8) * w = 8 * rb * w + 7 * w + w := by ring
    have e3 : (c + 1) * R = c * R + R := by ring
    have hchunk : (Native.rowChunks M w logH k).getD c .empty =
        encode (M.extract (c * (R * w)) (c * (R * w) + R * w)) := by
      simp only [Native.rowChunks]
      exact getD_map_range _ _ _ (by omega) _
    let Mc := M.extract (c * (R * w)) (c * (R * w) + R * w)
    have hMc : Mc.size = R * w := by simp only [Mc, Array.size_extract]; omega
    have hq : (8 * rb * w + 8 * s).toUSize.toNat = 8 * rb * w + 8 * s :=
      USize.toNat_ofNat_of_lt' (by omega)
    have hp : (8 * (c * R + 8 * rb)).toUSize.toNat = 8 * (c * R + 8 * rb) :=
      USize.toNat_ofNat_of_lt' (by simp only [N] at hN; omega)
    have hf := Native.fill_lines8 T N (8 * (c * R + 8 * rb)).toUSize 8 hN (by
        rw [hp, Native.usize_numeral 8 (by decide)]
        simp only [N]
        omega)
      (fun t u ↦ (Mc.getD (((8 * rb * w + 8 * s).toUSize + OfNat.ofNat t * w.toUSize).toNat +
        (OfNat.ofNat u : USize).toNat) 0).val) (by
        intro t ht u hu
        have htw : t * w ≤ 7 * w := Nat.mul_le_mul_right w (by omega)
        have hqt : ((8 * rb * w + 8 * s).toUSize + OfNat.ofNat t * w.toUSize).toNat =
            8 * rb * w + 8 * s + t * w := by
          rw [Native.usize_add_mul_numeral _ _ t (by omega) (by rw [hq, hwU]; omega), hq, hwU]
        rw [hqt, Native.usize_numeral u (by omega), hp, Native.usize_numeral 8 (by decide)]
        simp only [T, Mc]
        have hd : (8 * (c * R + 8 * rb) + t * 8 + u) / 8 = c * R + 8 * rb + t := by omega
        have hm : (8 * (c * R + 8 * rb) + t * 8 + u) % 8 = u := by omega
        rw [hd, hm, getD_extract_in _ _ _ _ (by omega) (by omega)]
        congr 2
        ring)
    refine (hf.congr_encode fun o ho ↦ ?_).mono ?_
    · have hRw : R * w ≤ M.size := by
        have := hcRw
        rw [e1, hKR] at this
        omega
      rw [hchunk, Native.stripCopy8_eq_lines8 Mc _ _ _ _ (by rw [hq, hwU, hMc]; omega)
        (by rw [hMc]; omega) (by rw [size_encode_uint32, hp, ho]; simp only [N]; omega)
        (by rw [size_encode_uint32, ho]; omega)]
    · rintro i ⟨t, ht, u, hu, rfl⟩
      exact ⟨t, ht, u, hu, by rw [hp, Native.usize_numeral 8 (by decide)]⟩
  unfold Native.stripOfChunks
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero, List.forIn_pure_yield_eq_foldl, bind_pure,
    Id.run_pure, Native.zeroWords_eq, hms, pure_bind]
  have hinner (c : Nat) (hc : c ∈ List.range' 0 K) :=
    Native.Fill.foldl T _ N (List.range' 0 (R / 8)) (fun b rb ↦ Native.stripCopy8
      ((Native.rowChunks M w logH k).getD c .empty) (8 * rb * w + 8 * s).toUSize w.toUSize b
      (8 * (c * R + 8 * rb)).toUSize) (htile c hc)
  have hall := Native.Fill.foldl T _ N (List.range' 0 K) _ hinner
  rw [hall.eq_ofFn (fun i hi ↦ ?_) _ Array.size_replicate, encode_eq_map_val]
  · congr 1
    apply Array.ext (by simp only [Array.size_ofFn, Array.size_map, stripOf, N]; rw [hR])
    intro i h1 _
    simp only [Array.getElem_ofFn, Array.getElem_map, stripOf, T]
  · obtain ⟨r, u, hu, rfl⟩ : ∃ r u, u < 8 ∧ i = 8 * r + u :=
      ⟨i / 8, i % 8, Nat.mod_lt _ (by decide), by omega⟩
    have hr : r < K * R := by simp only [N] at hi; omega
    have hRp : 0 < R := by
      rcases Nat.eq_zero_or_pos R with h0 | h0
      · rw [h0, Nat.mul_zero] at hr; omega
      · exact h0
    obtain ⟨c, r', hr', rfl⟩ : ∃ c r', r' < R ∧ r = c * R + r' :=
      ⟨r / R, r % R, Nat.mod_lt _ hRp, by rw [Nat.mul_comm]; exact (Nat.div_add_mod r R).symm⟩
    have hc : c < K := by
      by_contra hcK
      have : K * R ≤ c * R := Nat.mul_le_mul_right R (by omega)
      omega
    refine ⟨c, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, r' / 8,
      List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, r' % 8, Nat.mod_lt _ (by decide), u, hu,
      by omega⟩

/-- A strip's lane is a column of the matrix. -/
theorem lane8_stripOf (M : Array (FastField p)) (w s h l : Nat) (hl : l < 8) :
    lane8 (stripOf M w s h) h l = (column M w h (8 * s + l)).toArray := by
  unfold lane8 column
  rw [Vector.toArray_ofFn]
  congr 1
  funext r
  have hr := r.isLt
  rw [stripOf, getD_ofFn_bounded _ _ (by omega)]
  have h1 : (8 * r.val + l) / 8 = r.val := by omega
  have h2 : (8 * r.val + l) % 8 = l := by omega
  simp only [h1, h2]
  congr 1
  ring

/-- A coset block's first layers and passes, column by column, are the column's DIF transform:
`fieldLayers` split after its first layers. -/
theorem lane8_stripBlockField (D : NTT.Domain (FastField p)) (hm : 1 ≤ D.logN)
    (X : Array (FastField p)) (hX : X.size = 8 * 2 ^ D.logN) (l : Nat) (hl : l < 8) :
    lane8 (stripPasses (Plan.twiddleTable D) D.logN (1 - D.logN % 2)
      (firstLayers (Plan.twiddleTable D) D.logN X)) (2 ^ D.logN) l =
      difSpec D (lane8 X (2 ^ D.logN) l) := by
  have hfs : (firstLayers (Plan.twiddleTable D) D.logN X).size = 8 * 2 ^ D.logN := by
    unfold firstLayers
    split <;> simp only [Plan.size_butterflyDIFInner, Plan.size_butterflyDIFRadix4Blocks, hX]
  rw [lane8_stripPasses _ _ _ _ hfs l hl,
    ← planStages_eq_difSpec D (lane8 X (2 ^ D.logN) l) (size_lane8 _ _ _),
    ← fieldLayers_eq D _ (lane8 X (2 ^ D.logN) l) (size_lane8 _ _ _), fieldLayers_eq_difPasses]
  unfold firstLayers
  split
  · rename_i hodd
    have h2 : 2 ^ D.logN = 2 * 2 ^ (D.logN - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    have key := lane8_butterflyDIFInner ((Plan.twiddleTable D).getD (D.logN - 1) #[])
      (2 ^ (D.logN - 1)) X (by rw [hX, h2]) l hl
    rw [← h2] at key
    rw [key, show 1 - D.logN % 2 = 0 by omega]
  · rename_i heven
    have h4 : 2 ^ D.logN = 4 * 2 ^ (D.logN - 2) * 1 := by
      rw [Nat.mul_one, show 4 = 2 ^ 2 by rfl, ← Nat.pow_add]; congr 1; omega
    have key := lane8_butterflyDIFRadix4Blocks ((Plan.twiddleTable D).getD (D.logN - 1) #[])
      ((Plan.twiddleTable D).getD (D.logN - 2) #[]) (2 ^ (D.logN - 2)) 1 (Nat.two_pow_pos _) X
      (by rw [hX, ← h4]) l hl
    rw [← h4] at key
    have hm2 : 0 < D.logN / 2 := by omega
    rw [key, show 1 - D.logN % 2 = 0 + 1 by omega,
      difPasses_succ (Plan.twiddleTable D) D.logN 0 hm2 (lane8 X (2 ^ D.logN) l)]
    have e3 : 2 ^ D.logN / (4 * 2 ^ (D.logN - 2)) = 1 := by
      rw [h4, Nat.mul_one, Nat.div_self (by positivity)]
    simp only [show D.logN - 1 - D.logN % 2 - 2 * 0 = D.logN - 1 by omega,
      show D.logN - 1 - 1 = D.logN - 2 by omega, e3]

/-- The coefficients of a column, stored in bit-reversed order by its DIF transform, scaled by a
coset table read in natural order. -/
theorem lane8_scaledRows (D : NTT.Domain (FastField p)) (m : Nat) (hDm : D.logN = m)
    (T C : Array (FastField p)) (cols : Nat → Array (FastField p))
    (hC : ∀ l < 8, lane8 C (2 ^ m) l = difSpec D.inverse (cols l)) (l : Nat) (hl : l < 8) :
    lane8 (scaledRows T C m) (2 ^ m) l = Array.ofFn (n := 2 ^ m) fun i ↦
      T.getD i.val 0 * (NTT.Forward.forwardSpec D.inverse (cols l)).getD i.val 0 := by
  subst hDm
  unfold lane8
  congr 1
  funext i
  have hi := i.isLt
  have hb : NTT.Transform.bitRevNat D.logN i.val < 2 ^ D.logN := NTT.Transform.bitRevNat_lt _ _
  rw [scaledRows, getD_ofFn_bounded _ _ (by omega)]
  have h1 : (8 * i.val + l) / 8 = i.val := by omega
  have h2 : (8 * i.val + l) % 8 = l := by omega
  simp only [h1, h2]
  have hlane := getD_lane8 C (2 ^ D.logN) l _ hb
  have hinv : D.inverse.logN = D.logN := rfl
  rw [hC l hl, getD_difSpec D.inverse _ _ hb, hinv,
    NTT.Transform.bitRevNat_involutive D.logN i.val hi] at hlane
  rw [← hlane, NTT.Forward.forwardSpec, getD_ofFn_bounded _ _ (show i.val < D.inverse.n from hi)]
  exact congrArg (T.getD i.val 0 * ·) (dftValue_eq_nttAt D.inverse (cols l) ⟨i.val, hi⟩)

/-- `lane8_scaledRows` at a plan's coefficient domain. -/
theorem lane8_scaledRows_plan (P : LdePlan p) (S T C : Array (FastField p))
    (hC : ∀ l < 8, lane8 C (2 ^ P.logH) l = difSpec P.low.inverse (lane8 S (2 ^ P.logH) l))
    (l : Nat) (hl : l < 8) :
    lane8 (scaledRows T C P.logH) (2 ^ P.logH) l = Array.ofFn (n := 2 ^ P.logH) fun i ↦
      T.getD i.val 0 * (NTT.Forward.forwardSpec P.low.inverse (lane8 S (2 ^ P.logH) l)).getD
        i.val 0 :=
  lane8_scaledRows P.low P.logH rfl T C (fun l ↦ lane8 S (2 ^ P.logH) l) hC l hl

/-! ### Extension -/

/-- **Block `t` of a strip's extension is its columns' blocks**: the strip's coefficients'
coset block `t`, split into columns, is every column's coset block `t` of its coefficients. -/
theorem Native.stripBlock_stripCoefficients (P : LdePlan p) (S : Array (FastField p))
    (hS : S.size = 8 * 2 ^ P.logH) (hm : 1 ≤ P.logH) (h8 : 3 ≤ P.logH)
    (hu : 4 * (8 * 2 ^ P.logH) < USize.size) (t : Nat) :
    Native.stripBlock P (Native.stripCoefficients P (encode S)) t =
      (Array.range 8).map fun l ↦
        Native.cosetBlock P (Native.columnCoefficients P (encode (lane8 S (2 ^ P.logH) l))) t := by
  have h32 : P.logH ≤ 32 := by have := P.log_bound; simp only [LdePlan.logH]; omega
  obtain ⟨htwI, honeI⟩ := twiddleTable_invariants P.low.inverse
  obtain ⟨htwF, honeF⟩ := twiddleTable_invariants P.low
  -- The coefficients.
  have hC : Native.stripCoefficients P (encode S) =
      encode (stripLayersField (Plan.twiddleTable P.low.inverse) P.logH S) := by
    unfold Native.stripCoefficients
    rw [P.inverse_eq]
    exact Native.stripLayers_encode _ P.logH htwI honeI S hS hu
  let C := stripLayersField (Plan.twiddleTable P.low.inverse) P.logH S
  have hCs : C.size = 8 * 2 ^ P.logH := by
    simp only [C, stripLayersField, size_stripPasses]
    split <;> simp only [Plan.size_butterflyDIFInner, hS]
  have hClane (l : Nat) (hl : l < 8) :
      lane8 C (2 ^ P.logH) l = difSpec P.low.inverse (lane8 S (2 ^ P.logH) l) :=
    lane8_stripLayersField P.low.inverse S hS l hl
  -- The coset table.
  let T := cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t)
  have hT : P.cosetTables.getD (NTT.Transform.bitRevNat P.bits t) .empty = encode T := by
    rw [P.tables_eq, getD_map_range _ _ _ (NTT.Transform.bitRevNat_lt _ _)]
  have hTs : T.size = 2 ^ P.logH := size_cosetTable _ _ _ _
  -- The block.
  let X := scaledRows T C P.logH
  have hXs : X.size = 8 * 2 ^ P.logH := by simp only [X, scaledRows, Array.size_ofFn]
  have hY : (firstLayers (Plan.twiddleTable P.low) P.logH X).size = 8 * 2 ^ P.logH := by
    unfold firstLayers
    split <;> simp only [Plan.size_butterflyDIFInner, Plan.size_butterflyDIFRadix4Blocks, hXs]
  unfold Native.stripBlock
  rw [hC, hT, P.forward_eq]
  dsimp only
  rw [Native.stripScaled_encode _ P.logH hm h32 htwF T C hTs hCs hu,
    Native.stripLayersFrom_encode _ P.logH _ htwF honeF _ hY hu,
    Native.stripColumns_encode _ _ (Nat.pow_dvd_pow 2 h8)
      (by rw [size_stripPasses, hY]) hu]
  apply Array.ext (by simp only [Array.size_map, Array.size_range])
  intro l hl _
  simp only [Array.size_map, Array.size_range] at hl
  simp only [Array.getElem_map, Array.getElem_range]
  rw [Native.columnCoefficients_encode P _ (size_lane8 _ _ _),
    Native.cosetBlock_encode P _ (by rw [NTT.Forward.size_forwardSpec]; rfl) t]
  apply congrArg encode
  have key := lane8_stripBlockField P.low hm X hXs l hl
  have hlog : P.low.logN = P.logH := rfl
  rw [hlog] at key
  rw [key]
  have hr : P.low.inverse.logN = P.logH := rfl
  rw [show X = scaledRows T C P.logH from rfl,
    show cosetTable P.domain P.bits P.shift (NTT.Transform.bitRevNat P.bits t) = T from rfl]
  clear_value X C T
  exact congrArg (difSpec P.low) (lane8_scaledRows_plan P S T C hClane l hl)

end Kernels

end CompPoly.CPolynomial.NTTFast.Packed
