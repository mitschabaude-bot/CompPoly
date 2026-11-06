/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Native
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.MatrixSpec
/-! # Refinement of packed four-bit combination tables -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
namespace AdditiveNTT.Bitsliced
open BF64

/-- The scratch bytes as the existing certified packed storage type. -/
def Scratch.packed (s : Scratch) : BF64.Packed.Buffer 256 :=
  ⟨⟨256, s.val, s.property⟩, rfl⟩

/-- Aligned scratch offsets select the same word as the packed accessor. -/
theorem Scratch.read_eq_packed (s : Scratch) (i : USize) (hi : i.toNat ≤ 2040)
    (ha : i.toNat % 8 = 0) :
    s.read i hi = (BF64.Packed.read s.packed ⟨i.toNat / 8, by omega⟩).val := by
  have he : 8 * (i.toNat / 8) = i.toNat := by omega
  have hp : (i + 4).toNat = i.toNat + 4 := by
    simpa only [Native.small 4 (by decide)] using
      Native.add_toNat i 4 (by rw [Native.small 4 (by decide)]; omega)
  simp only [Scratch.read, Scratch.packed, BF64.Packed.read, BF64.Packed.get,
    ByteArray.ugetUInt32LE, ByteArray.getUInt32LE, hp, he]

/-- Aligned scratch stores are the certified packed stores. -/
theorem Scratch.packed_write (s : Scratch) (i : USize) (hi : i.toNat ≤ 2040)
    (ha : i.toNat % 8 = 0) (v : UInt64) :
    (s.write i hi v).packed = BF64.Packed.write s.packed ⟨i.toNat / 8, by omega⟩ ⟨v⟩ := by
  have he : 8 * (i.toNat / 8) = i.toNat := by omega
  have hp : (i + 4).toNat = i.toNat + 4 := by
    simpa only [Native.small 4 (by decide)] using
      Native.add_toNat i 4 (by rw [Native.small 4 (by decide)]; omega)
  simp only [Scratch.write, Scratch.packed, BF64.Packed.write, BF64.Packed.set,
    ByteArray.usetUInt32LE, hp, he]

/-- A four-bit index selects exactly the indicated XOR combination. -/
theorem Chunk.get_create (a b c d : UInt64) (i : Fin 16) :
    (Chunk.create a b c d).get (UInt64.ofNat i.val) =
      (if Nat.testBit i.val 0 then a else 0) ^^^
      (if Nat.testBit i.val 1 then b else 0) ^^^
      (if Nat.testBit i.val 2 then c else 0) ^^^
      (if Nat.testBit i.val 3 then d else 0) := by
  fin_cases i <;> simp [Chunk.create, Chunk.get, Nat.testBit,
    UInt64.xor_zero, UInt64.zero_xor] <;> ac_rfl

/-- The register combination belonging to a scratch slot. -/
def scratchValue (a : Block) (q : Fin 256) : UInt64 :=
  let g := q.val / 16
  let v := Chunk.create (a.get ⟨4 * g, by have := q.isLt; dsimp [g]; omega⟩)
    (a.get ⟨4 * g + 1, by have := q.isLt; dsimp [g]; omega⟩)
    (a.get ⟨4 * g + 2, by have := q.isLt; dsimp [g]; omega⟩)
    (a.get ⟨4 * g + 3, by have := q.isLt; dsimp [g]; omega⟩)
  v.get (UInt64.ofNat (q.val % 16))

/-- Machine offsets preserve the selected group and nibble. -/
theorem nibbleOffset_toNat (g : USize) (hg : g.toNat < 16) (v : UInt64) :
    (nibbleOffset g v).toNat = 8 * (16 * g.toNat + (v &&& 15).toNat) := by
  have hv : (v &&& 15).toNat < 16 := by
    rw [UInt64.toNat_and]
    exact Nat.and_lt_two_pow _ (by decide : (15 : UInt64).toNat < 2 ^ 4)
  have hc : (v &&& 15).toUSize.toNat = (v &&& 15).toNat := by
    rw [UInt64.toNat_toUSize, Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]
  simp only [nibbleOffset, USize.toNat_add, USize.toNat_mul, Native.small 128 (by decide),
    Native.small 8 (by decide), hc]
  have h1 : g.toNat * 128 < 2 ^ System.Platform.numBits :=
    lt_of_lt_of_le (by omega) USize.le_size
  have h2 : (v &&& 15).toNat * 8 < 2 ^ System.Platform.numBits :=
    lt_of_lt_of_le (by omega) USize.le_size
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]
  omega

/-- Overwrite one contiguous group in the mathematical packed model. -/
def fillGroup (b : BF64.Packed.Buffer 256) (g : Fin 16) (t : Chunk) : BF64.Packed.Buffer 256 :=
  Fin.foldl 16 (fun b j => BF64.Packed.write b
    ⟨16 * g.val + j.val, by have := g.isLt; have := j.isLt; omega⟩
    ⟨t.get (UInt64.ofNat j.val)⟩) b

/-- Each packed table group contains the sixteen register combinations. -/
theorem fillChunk_packed (s : Scratch) (g : USize) (hg : g.toNat < 16) (t : Chunk) :
    (fillChunk s g hg t).packed =
      fillGroup s.packed ⟨g.toNat, hg⟩ t := by
  have h0 : (g * 128 + 0).toNat = 128 * g.toNat + 0 := by
    rw [chunkOffset_toNat g 0 hg (by rw [Native.small 0 (by decide)]; omega),
      Native.small 0 (by decide)]
    omega
  have h1 : (g * 128 + 8).toNat = 128 * g.toNat + 8 := by
    rw [chunkOffset_toNat g 8 hg (by rw [Native.small 8 (by decide)]; omega),
      Native.small 8 (by decide)]
    omega
  have h2 : (g * 128 + 16).toNat = 128 * g.toNat + 16 := by
    rw [chunkOffset_toNat g 16 hg (by rw [Native.small 16 (by decide)]; omega),
      Native.small 16 (by decide)]
    omega
  have h3 : (g * 128 + 24).toNat = 128 * g.toNat + 24 := by
    rw [chunkOffset_toNat g 24 hg (by rw [Native.small 24 (by decide)]; omega),
      Native.small 24 (by decide)]
    omega
  have h4 : (g * 128 + 32).toNat = 128 * g.toNat + 32 := by
    rw [chunkOffset_toNat g 32 hg (by rw [Native.small 32 (by decide)]; omega),
      Native.small 32 (by decide)]
    omega
  have h5 : (g * 128 + 40).toNat = 128 * g.toNat + 40 := by
    rw [chunkOffset_toNat g 40 hg (by rw [Native.small 40 (by decide)]; omega),
      Native.small 40 (by decide)]
    omega
  have h6 : (g * 128 + 48).toNat = 128 * g.toNat + 48 := by
    rw [chunkOffset_toNat g 48 hg (by rw [Native.small 48 (by decide)]; omega),
      Native.small 48 (by decide)]
    omega
  have h7 : (g * 128 + 56).toNat = 128 * g.toNat + 56 := by
    rw [chunkOffset_toNat g 56 hg (by rw [Native.small 56 (by decide)]; omega),
      Native.small 56 (by decide)]
    omega
  have h8 : (g * 128 + 64).toNat = 128 * g.toNat + 64 := by
    rw [chunkOffset_toNat g 64 hg (by rw [Native.small 64 (by decide)]; omega),
      Native.small 64 (by decide)]
    omega
  have h9 : (g * 128 + 72).toNat = 128 * g.toNat + 72 := by
    rw [chunkOffset_toNat g 72 hg (by rw [Native.small 72 (by decide)]; omega),
      Native.small 72 (by decide)]
    omega
  have h10 : (g * 128 + 80).toNat = 128 * g.toNat + 80 := by
    rw [chunkOffset_toNat g 80 hg (by rw [Native.small 80 (by decide)]; omega),
      Native.small 80 (by decide)]
    omega
  have h11 : (g * 128 + 88).toNat = 128 * g.toNat + 88 := by
    rw [chunkOffset_toNat g 88 hg (by rw [Native.small 88 (by decide)]; omega),
      Native.small 88 (by decide)]
    omega
  have h12 : (g * 128 + 96).toNat = 128 * g.toNat + 96 := by
    rw [chunkOffset_toNat g 96 hg (by rw [Native.small 96 (by decide)]; omega),
      Native.small 96 (by decide)]
    omega
  have h13 : (g * 128 + 104).toNat = 128 * g.toNat + 104 := by
    rw [chunkOffset_toNat g 104 hg (by rw [Native.small 104 (by decide)]; omega),
      Native.small 104 (by decide)]
    omega
  have h14 : (g * 128 + 112).toNat = 128 * g.toNat + 112 := by
    rw [chunkOffset_toNat g 112 hg (by rw [Native.small 112 (by decide)]; omega),
      Native.small 112 (by decide)]
    omega
  have h15 : (g * 128 + 120).toNat = 128 * g.toNat + 120 := by
    rw [chunkOffset_toNat g 120 hg (by rw [Native.small 120 (by decide)]),
      Native.small 120 (by decide)]
    omega
  have hmul : 128 * g.toNat / 8 = 16 * g.toNat := by omega
  have hdiv (j : Nat) : (128 * g.toNat + j) / 8 = 16 * g.toNat + j / 8 := by omega
  unfold fillGroup
  simp (disch := (simp only [h0, h1, h2, h3, h4, h5, h6, h7,
      h8, h9, h10, h11, h12, h13, h14, h15]; omega)) only
    [fillChunk, Scratch.packed_write, h0, h1, h2, h3, h4, h5, h6, h7,
      h8, h9, h10, h11, h12, h13, h14, h15]
  simp only [Fin.foldl_succ_last, Fin.foldl_zero, Fin.val_castSucc, Fin.val_last]
  simp [Chunk.get, hdiv, hmul]

/-- Reading a sequence of overwrites depends only on whether its index was visited. -/
theorem read_filling (index : Fin k → Fin n) (f : Fin n → BF64.Word)
    (a : BF64.Packed.Buffer n) (q : Fin n) :
    BF64.Packed.read (Fin.foldl k (fun a j => BF64.Packed.write a (index j) (f (index j))) a) q =
      if q ∈ (List.finRange k).map index then f q else BF64.Packed.read a q := by
  have aux (xs : List (Fin k)) (a : BF64.Packed.Buffer n) :
      BF64.Packed.read (xs.foldl (fun a j => BF64.Packed.write a (index j) (f (index j))) a) q =
        if q ∈ xs.map index then f q else BF64.Packed.read a q := by
    induction xs generalizing a with
    | nil => rfl
    | cons j xs ih =>
      rw [List.foldl_cons, ih, BF64.Packed.read_write]
      by_cases h : q ∈ xs.map index
      · simp only [List.map_cons, List.mem_cons, h, or_true, ite_true]
      · by_cases he : index j = q
        · subst q; simp only [List.map_cons, List.mem_cons, true_or, ite_true, h, ite_false]
        · simp only [List.map_cons, List.mem_cons, h, or_false, Ne.symm he, he, ite_false]
  rw [Fin.foldl_eq_finRange_foldl]
  exact aux _ a

/-- The four source planes belonging to a table group. -/
def sourceChunk (a : Block) (g : Fin 16) : Chunk :=
  Chunk.create (a.get ⟨4 * g.val, by have := g.isLt; omega⟩)
    (a.get ⟨4 * g.val + 1, by have := g.isLt; omega⟩)
    (a.get ⟨4 * g.val + 2, by have := g.isLt; omega⟩)
    (a.get ⟨4 * g.val + 3, by have := g.isLt; omega⟩)

/-- The table-fill sequence is a nested sweep over groups and combinations. -/
theorem Scratch.packed_prepare (s : Scratch) (a : Block) :
    (prepareScratch s a).packed = Fin.foldl 16 (fun b g =>
      fillGroup b g (sourceChunk a g)) s.packed := by
  simp (disch := decide) only [prepareScratch, prepareChunk, fillChunk_packed, Native.small]
  simp only [Fin.foldl_succ_last, Fin.foldl_zero]
  rfl

/-- A group fill changes only its sixteen slots. -/
theorem read_fillGroup (b : BF64.Packed.Buffer 256) (g : Fin 16) (t : Chunk) (q : Fin 256) :
    BF64.Packed.read (fillGroup b g t) q =
      if q.val / 16 = g.val then ⟨t.get (UInt64.ofNat (q.val % 16))⟩
      else BF64.Packed.read b q := by
  let index (j : Fin 16) : Fin 256 := ⟨16 * g.val + j.val, by
    have := g.isLt; have := j.isLt; omega⟩
  let f (q : Fin 256) : Word := ⟨t.get (UInt64.ofNat (q.val % 16))⟩
  have he : fillGroup b g t =
      Fin.foldl 16 (fun b j => BF64.Packed.write b (index j) (f (index j))) b := by
    unfold fillGroup
    apply congrArg (fun f : BF64.Packed.Buffer 256 → Fin 16 → BF64.Packed.Buffer 256 =>
      Fin.foldl 16 f b)
    funext b j
    have hj : (16 * g.val + j.val) % 16 = j.val := by have := j.isLt; omega
    simp only [index, f, hj]
  rw [he, read_filling]
  have hm : q ∈ (List.finRange 16).map index ↔ q.val / 16 = g.val := by
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      dsimp [index] at hv
      have := j.isLt
      omega
    · intro h
      refine ⟨⟨q.val % 16, Nat.mod_lt _ (by decide)⟩, Fin.ext ?_⟩
      dsimp [index]
      omega
  simp only [hm, f]

/-- Every prepared scratch slot is its four-plane XOR combination. -/
theorem Scratch.read_prepare (s : Scratch) (a : Block) (q : Fin 256) :
    BF64.Packed.read (prepareScratch s a).packed q = ⟨scratchValue a q⟩ := by
  let g : Fin 16 := ⟨q.val / 16, by have := q.isLt; omega⟩
  have aux (xs : List (Fin 16)) (b : BF64.Packed.Buffer 256) :
      BF64.Packed.read (xs.foldl (fun b g => fillGroup b g (sourceChunk a g)) b) q =
        if g ∈ xs then ⟨(sourceChunk a g).get (UInt64.ofNat (q.val % 16))⟩
        else BF64.Packed.read b q := by
    induction xs generalizing b with
    | nil => rfl
    | cons j xs ih =>
      rw [List.foldl_cons, ih, read_fillGroup]
      by_cases h : g ∈ xs
      · simp only [List.mem_cons, h, or_true, ite_true]
      · by_cases he : j = g
        · subst j
          simp only [List.mem_cons, true_or, ite_true, h, ite_false, g]
        · have hn : q.val / 16 ≠ j.val := by
            intro hv
            exact he (Fin.ext hv.symm)
          simp only [List.mem_cons, Ne.symm he, h, false_or, ite_false, hn]
  rw [Scratch.packed_prepare, Fin.foldl_eq_finRange_foldl, aux,
    ite_eq_left (List.mem_finRange g)]
  rfl

/-- A prepared lookup selects its source group's requested combination. -/
theorem lookup_prepare (s : Scratch) (a : Block) (g : USize) (hg : g.toNat < 16) (v : UInt64) :
    (prepareScratch s a).lookup g hg v =
      (sourceChunk a ⟨g.toNat, hg⟩).get (v &&& 15) := by
  have hv : (v &&& 15).toNat < 16 := by
    rw [UInt64.toNat_and]
    exact Nat.and_lt_two_pow _ (by decide : (15 : UInt64).toNat < 2 ^ 4)
  let q : Fin 256 := ⟨16 * g.toNat + (v &&& 15).toNat, by omega⟩
  have hdiv : q.val / 16 = g.toNat := by dsimp [q]; omega
  have hmod : q.val % 16 = (v &&& 15).toNat := by dsimp [q]; omega
  have hr : (prepareScratch s a).lookup g hg v =
      (BF64.Packed.read (prepareScratch s a).packed q).val := by
    unfold Scratch.lookup
    rw [Scratch.read_eq_packed _ _ _ (by rw [nibbleOffset_toNat g hg]; omega)]
    congr 2
    apply Fin.ext
    change (nibbleOffset g v).toNat / 8 = q.val
    rw [nibbleOffset_toNat g hg]
    dsimp [q]
    omega
  rw [hr, Scratch.read_prepare]
  simp only [scratchValue, hdiv, hmod, UInt64.ofNat_toNat, sourceChunk]

/-- Word XOR is addition in the specification field. -/
theorem toField_xor (a b : UInt64) :
    Word.toField ⟨a ^^^ b⟩ = Word.toField ⟨a⟩ + Word.toField ⟨b⟩ :=
  Word.toField_add ⟨a⟩ ⟨b⟩

/-- A selected word is the corresponding conditional field summand. -/
theorem toField_ite (b : Bool) (a : UInt64) :
    Word.toField ⟨if b then a else 0⟩ = if b then Word.toField ⟨a⟩ else 0 := by
  cases b <;> rfl

/-- A masked nibble's bits are the corresponding bits of its matrix row. -/
theorem nibble_bit (m : UInt64) (g : Fin 16) (k : Fin 4) :
    Nat.testBit ((m >>> UInt64.ofNat (4 * g.val)) &&& 15).toNat k.val =
      m.toBitVec.getLsbD (4 * g.val + k.val) := by
  have hg : 4 * g.val < 64 := by have := g.isLt; omega
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat_of_lt' (lt_trans hg (by decide : 64 < UInt64.size)),
    Nat.mod_eq_of_lt hg, Nat.testBit_and, Nat.testBit_shiftRight]
  have hk : Nat.testBit (15 : UInt64).toNat k.val = true := by fin_cases k <;> decide
  simp only [hk, Bool.and_true, BitVec.getLsbD]
  rfl

/-- A four-bit table lookup is the sum of its four binary matrix entries. -/
theorem lookup_toField (s : Scratch) (a : Block) (m : UInt64) (g : Fin 16) :
    Word.toField ⟨(prepareScratch s a).lookup (USize.ofNat g.val)
      (by rw [Native.ofNat_toNat g.val (by have := g.isLt; omega)]; exact g.isLt)
      (m >>> UInt64.ofNat (4 * g.val))⟩ =
      ∑ k : Fin 4, if m.toBitVec.getLsbD (4 * g.val + k.val) then
        Word.toField ⟨a.get ⟨4 * g.val + k.val, by have := g.isLt; have := k.isLt; omega⟩⟩
      else 0 := by
  let v := m >>> UInt64.ofNat (4 * g.val)
  have hv : (v &&& 15).toNat < 16 := by
    rw [UInt64.toNat_and]
    exact Nat.and_lt_two_pow _ (by decide : (15 : UInt64).toNat < 2 ^ 4)
  have hc := Chunk.get_create
    (a.get ⟨4 * g.val, by have := g.isLt; omega⟩)
    (a.get ⟨4 * g.val + 1, by have := g.isLt; omega⟩)
    (a.get ⟨4 * g.val + 2, by have := g.isLt; omega⟩)
    (a.get ⟨4 * g.val + 3, by have := g.isLt; omega⟩) ⟨(v &&& 15).toNat, hv⟩
  simp only [UInt64.ofNat_toNat] at hc
  rw [lookup_prepare]
  simp only [Native.ofNat_toNat g.val (by have := g.isLt; omega), sourceChunk]
  rw [hc]
  simp only [toField_xor, toField_ite]
  simp only [v, nibble_bit m g ⟨0, by decide⟩, nibble_bit m g ⟨1, by decide⟩,
    nibble_bit m g ⟨2, by decide⟩, nibble_bit m g ⟨3, by decide⟩]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    add_zero, add_assoc]
  rfl

/-- The unrolled table dot product is the field's binary dot product. -/
theorem dotScratch_toField (s : Scratch) (m : UInt64) (a : Block) :
    Word.toField ⟨dotScratch (prepareScratch s a) m⟩ = dotSpec m a := by
  have hsplit : dotSpec m a = ∑ g : Fin 16, ∑ k : Fin 4,
      if m.toBitVec.getLsbD (4 * g.val + k.val) then
        Word.toField ⟨a.get ⟨4 * g.val + k.val, by have := g.isLt; have := k.isLt; omega⟩⟩
      else 0 := by
    unfold dotSpec
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      BitVec.getLsb, add_zero, add_assoc]
    rfl
  have hdot : Word.toField ⟨dotScratch (prepareScratch s a) m⟩ =
      ∑ g : Fin 16, Word.toField ⟨(prepareScratch s a).lookup (USize.ofNat g.val)
        (by rw [Native.ofNat_toNat g.val (by have := g.isLt; omega)]; exact g.isLt)
        (m >>> UInt64.ofNat (4 * g.val))⟩ := by
    simp only [dotScratch, toField_xor, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Fin.val_zero, Fin.val_succ, add_zero, add_assoc]
    rfl
  rw [hdot, hsplit]
  exact Finset.sum_congr rfl (fun g _ => lookup_toField s a m g)

/-- Every native output plane is its binary matrix dot product. -/
theorem applyScratch_get (s : Scratch) (m a : Block) (i : Fin 64) :
    (applyScratch (prepareScratch s a) m).get i = dotScratch (prepareScratch s a) (m.get i) := by
  fin_cases i <;> rfl

/-- Packed four-bit table multiplication refines the mathematical matrix application. -/
theorem applyScratch_eq_applySpec (s : Scratch) (t : UInt64) (a : Block) :
    applyScratch (prepareScratch s a) (matrix t) = applySpec t a := by
  apply Block.ext
  intro i
  suffices he : Word.toField ⟨(applyScratch (prepareScratch s a) (matrix t)).get i⟩ =
      Word.toField ⟨(applySpec t a).get i⟩ by
    exact congrArg Word.val (Word.toField_injective he)
  rw [applyScratch_get, dotScratch_toField, applySpec_get]

end AdditiveNTT.Bitsliced
