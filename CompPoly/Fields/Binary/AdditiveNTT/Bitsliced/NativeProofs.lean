/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Native
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Transpose
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.ScratchProofs
/-! # Row reads and writes refine packed storage -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace AdditiveNTT.Bitsliced.Native

/-- A checked machine offset has its ordinary natural-number address. -/
theorem row_offset_eq (base : USize) (hbase : base.toNat + 64 ≤ n)
    (hn : 8 * n < 4294967296) (i : Fin 64) :
    (base + USize.ofNat i.val).toNat = base.toNat + i.val := by
  rw [add_toNat _ _ (by rw [ofNat_toNat i.val (by have := i.isLt; omega)]; omega),
    ofNat_toNat i.val (by have := i.isLt; omega)]

/-- Loading a block recovers every packed row coordinate. -/
theorem load_get (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (base : USize) (hbase : base.toNat + 64 ≤ n) (i : Fin 64) :
    (load a hn base hbase).get i =
      (BF64.Packed.read a ⟨base.toNat + i.val, by have := i.isLt; omega⟩).val := by
  have he : (load a hn base hbase).get i =
      read a hn (base + USize.ofNat i.val) (row_offset base hbase hn i) := by
    fin_cases i <;> rfl
  rw [he, read_eq]
  congr 2
  exact Fin.ext (row_offset_eq base hbase hn i)

/-- Unrolled row stores agree with sixty-four certified packed writes. -/
theorem store_eq (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (base : USize) (hbase : base.toNat + 64 ≤ n) (v : Block) :
    store a hn base hbase v = Fin.foldl 64 (fun a i => BF64.Packed.write a
      ⟨base.toNat + i.val, by have := i.isLt; omega⟩ ⟨v.get i⟩) a := by
  simp only [store, write_eq]
  simp only [Fin.foldl_succ_last, Fin.foldl_zero, Fin.val_castSucc, Fin.val_last]
  have hs : 4294967296 ≤ 2 ^ System.Platform.numBits := USize.le_size
  simp only [USize.toNat_add, small 0 (by decide), small 1 (by decide), small 2 (by decide),
    small 3 (by decide), small 4 (by decide), small 5 (by decide), small 6 (by decide),
    small 7 (by decide), small 8 (by decide), small 9 (by decide), small 10 (by decide),
    small 11 (by decide), small 12 (by decide), small 13 (by decide), small 14 (by decide),
    small 15 (by decide), small 16 (by decide), small 17 (by decide), small 18 (by decide),
    small 19 (by decide), small 20 (by decide), small 21 (by decide), small 22 (by decide),
    small 23 (by decide), small 24 (by decide), small 25 (by decide), small 26 (by decide),
    small 27 (by decide), small 28 (by decide), small 29 (by decide), small 30 (by decide),
    small 31 (by decide), small 32 (by decide), small 33 (by decide), small 34 (by decide),
    small 35 (by decide), small 36 (by decide), small 37 (by decide), small 38 (by decide),
    small 39 (by decide), small 40 (by decide), small 41 (by decide), small 42 (by decide),
    small 43 (by decide), small 44 (by decide), small 45 (by decide), small 46 (by decide),
    small 47 (by decide), small 48 (by decide), small 49 (by decide), small 50 (by decide),
    small 51 (by decide), small 52 (by decide), small 53 (by decide), small 54 (by decide),
    small 55 (by decide), small 56 (by decide), small 57 (by decide), small 58 (by decide),
    small 59 (by decide), small 60 (by decide), small 61 (by decide), small 62 (by decide),
    small 63 (by decide)]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  rfl

/-- Row stores change precisely the words in their checked interval. -/
theorem read_store (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (base : USize) (hbase : base.toNat + 64 ≤ n) (v : Block) (q : Fin n) :
    BF64.Packed.read (store a hn base hbase v) q =
      if h : base.toNat ≤ q.val ∧ q.val < base.toNat + 64 then
        ⟨v.get ⟨q.val - base.toNat, by omega⟩⟩ else BF64.Packed.read a q := by
  let index (j : Fin 64) : Fin n := ⟨base.toNat + j.val, by have := j.isLt; omega⟩
  let f (q : Fin n) : BF64.Word :=
    if h : base.toNat ≤ q.val ∧ q.val < base.toNat + 64 then
      ⟨v.get ⟨q.val - base.toNat, by omega⟩⟩ else ⟨0⟩
  have he : store a hn base hbase v =
      Fin.foldl 64 (fun a j => BF64.Packed.write a (index j) (f (index j))) a := by
    rw [store_eq]
    apply congrArg (fun f : BF64.Packed.Buffer n → Fin 64 → BF64.Packed.Buffer n =>
      Fin.foldl 64 f a)
    funext a j
    have hj : base.toNat ≤ (index j).val ∧ (index j).val < base.toNat + 64 := by
      dsimp [index]; have := j.isLt; omega
    simp only [index, f, dite_eq_left hj, Nat.add_sub_cancel_left]
  rw [he, read_filling]
  have hm : q ∈ (List.finRange 64).map index ↔ base.toNat ≤ q.val ∧ q.val < base.toNat + 64 := by
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      dsimp [index] at hv
      have := j.isLt
      omega
    · intro h
      refine ⟨⟨q.val - base.toNat, by omega⟩, Fin.ext ?_⟩
      dsimp [index]
      omega
  simp only [hm, f]
  split <;> rfl

end AdditiveNTT.Bitsliced.Native

namespace AdditiveNTT.Bitsliced

/-- Mathematical row projection of a physical sixty-four-word buffer. -/
def readRow (a : BF64.Packed.Buffer (rows * 64)) (r : Fin rows) : Block :=
  Block.ofFn fun i => (BF64.Packed.read a
    ⟨r.val * 64 + i.val, by have := r.isLt; have := i.isLt; omega⟩).val

/-- A row has a checked machine address within the physical buffer. -/
theorem rowAddress (r : Fin rows) (hn : 8 * (rows * 64) < 4294967296) :
    (USize.ofNat (r.val * 64)).toNat + 64 ≤ rows * 64 := by
  rw [Native.ofNat_toNat (r.val * 64) (by have := r.isLt; omega)]
  have := r.isLt
  omega

/-- Store one mathematical row through the native packed accessor. -/
def writeRow (a : BF64.Packed.Buffer (rows * 64)) (hn : 8 * (rows * 64) < 4294967296)
    (r : Fin rows) (v : Block) : BF64.Packed.Buffer (rows * 64) :=
  Native.store a hn (USize.ofNat (r.val * 64)) (rowAddress r hn) v

/-- Native loading is the mathematical row projection. -/
theorem load_eq_readRow (a : BF64.Packed.Buffer (rows * 64))
    (hn : 8 * (rows * 64) < 4294967296) (r : Fin rows) :
    Native.load a hn (USize.ofNat (r.val * 64)) (rowAddress r hn) = readRow a r := by
  apply Block.ext
  intro i
  simp only [Native.load_get, readRow, Block.get_ofFn,
    Native.ofNat_toNat (r.val * 64) (by have := r.isLt; omega)]

/-- Row stores preserve every distinct row. -/
theorem readRow_writeRow (a : BF64.Packed.Buffer (rows * 64))
    (hn : 8 * (rows * 64) < 4294967296) (r q : Fin rows) (v : Block) :
    readRow (writeRow a hn r v) q = if r = q then v else readRow a q := by
  apply Block.ext
  intro i
  simp only [readRow, Block.get_ofFn, writeRow, Native.read_store,
    Native.ofNat_toNat (r.val * 64) (by have := r.isLt; omega)]
  by_cases h : r = q
  · subst r
    simp only [ite_true, dite_eq_left (show q.val * 64 ≤ q.val * 64 + i.val ∧
      q.val * 64 + i.val < q.val * 64 + 64 from by have := i.isLt; omega), Nat.add_sub_cancel_left]
  · have hh : ¬(r.val * 64 ≤ q.val * 64 + i.val ∧ q.val * 64 + i.val < r.val * 64 + 64) := by
      have hne : r.val ≠ q.val := fun he => h (Fin.ext he)
      have := i.isLt
      omega
    simp only [h, ite_false, dite_eq_right hh, Block.get_ofFn]

/-- A native address with the row's word offset loads that row. -/
theorem load_at (a : BF64.Packed.Buffer (rows * 64))
    (hn : 8 * (rows * 64) < 4294967296) (base : USize)
    (hb : base.toNat + 64 ≤ rows * 64) (r : Fin rows)
    (he : base.toNat = r.val * 64) : Native.load a hn base hb = readRow a r := by
  have hbase : base = USize.ofNat (r.val * 64) := by
    rw [← he]
    exact USize.ofNat_toNat.symm
  subst base
  exact load_eq_readRow a hn r

/-- A native address with the row's word offset stores that row. -/
theorem store_at (a : BF64.Packed.Buffer (rows * 64))
    (hn : 8 * (rows * 64) < 4294967296) (base : USize)
    (hb : base.toNat + 64 ≤ rows * 64) (r : Fin rows)
    (he : base.toNat = r.val * 64) (v : Block) :
    Native.store a hn base hb v = writeRow a hn r v := by
  have hbase : base = USize.ofNat (r.val * 64) := by
    rw [← he]
    exact USize.ofNat_toNat.symm
  subst base
  rfl

end AdditiveNTT.Bitsliced
