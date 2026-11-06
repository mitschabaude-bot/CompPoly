/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Refinement
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Codec
/-! # Input and output transposition for packed bit-plane encoders -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace AdditiveNTT.Bitsliced
open BF64

/-- Filling all rows recovers their defining blocks. -/
theorem read_rowFilling (f : Fin rows → Block) (a : Rows rows)
    (hn : 8 * (rows * 64) < 4294967296) (q : Fin rows) :
    readRow (Fin.foldl rows (fun a r => writeRow a hn r (f r)) a) q = f q := by
  have aux (xs : List (Fin rows)) (a : Rows rows) :
      readRow (xs.foldl (fun a r => writeRow a hn r (f r)) a) q =
        if q ∈ xs then f q else readRow a q := by
    induction xs generalizing a with
    | nil => rfl
    | cons r xs ih =>
      rw [List.foldl_cons, ih, readRow_writeRow]
      by_cases h : q ∈ xs
      · simp only [List.mem_cons, h, or_true, ite_true]
      · by_cases he : r = q
        · subst q; simp only [h, ite_false, List.mem_cons, true_or, ite_true]
        · simp only [List.mem_cons, Ne.symm he, h, false_or, he, ite_false]
  rw [Fin.foldl_eq_finRange_foldl, aux, ite_eq_left (List.mem_finRange q)]

/-- Input materialization fills the transposed row directly in packed bytes. -/
theorem read_fromFn (rows : Nat) (hn : 8 * (rows * 64) < 4294967296)
    (f : Fin rows → Fin 64 → UInt64) (r : Fin rows) :
    readRow (fromFn rows hn f) r = transpose (Block.ofFn (f r)) := by
  unfold fromFn
  rw [fold_eq]
  simp only [Native.ofNat_toNat rows (by omega), Fin.val_cast]
  simp (disch := omega) only [Native.ofNat_toNat]
  have hm (j : Fin rows) : USize.ofNat j.val * 64 = USize.ofNat (j.val * 64) :=
    (USize.ofNat_mul _ _).symm
  simp only [hm]
  exact read_rowFilling (fun j => transpose (Block.ofFn (f j))) _ hn r

/-- Every directly materialized bit-plane lane is its input word. -/
theorem lane_fromFn (rows : Nat) (hn : 8 * (rows * 64) < 4294967296)
    (f : Fin rows → Fin 64 → UInt64) (r : Fin rows) (c : Fin 64) :
    lane (readRow (fromFn rows hn f) r) c = ⟨f r c⟩ := by
  rw [read_fromFn]
  simp only [lane, transpose_transpose, Block.get_ofFn]

/-- Native row maps are the finite row overwrite model. -/
theorem mapRows_eq (a : Rows rows) (hn : 8 * (rows * 64) < 4294967296) (f : Block → Block) :
    mapRows a hn f = Fin.foldl rows (fun a r => writeRow a hn r (f (readRow a r))) a := by
  unfold mapRows
  rw [fold_eq]
  simp only [Native.ofNat_toNat rows (by omega), Fin.val_cast]
  have hm (j : Fin rows) : USize.ofNat j.val * 64 = USize.ofNat (j.val * 64) :=
    (USize.ofNat_mul _ _).symm
  simp only [hm]
  apply congrArg (fun g : Rows rows → Fin rows → Rows rows => Fin.foldl rows g a)
  funext a r
  rw [load_eq_readRow]
  rfl

/-- Each mapped row applies its operation to the input row exactly once. -/
theorem read_mapRows (a : Rows rows) (hn : 8 * (rows * 64) < 4294967296)
    (f : Block → Block) (q : Fin rows) :
    readRow (mapRows a hn f) q = f (readRow a q) := by
  have aux (xs : List (Fin rows)) (hx : xs.Nodup) (a : Rows rows) :
      readRow (xs.foldl (fun a r => writeRow a hn r (f (readRow a r))) a) q =
        if q ∈ xs then f (readRow a q) else readRow a q := by
    induction xs generalizing a with
    | nil => rfl
    | cons r xs ih =>
      rw [List.nodup_cons] at hx
      rw [List.foldl_cons, ih hx.2, readRow_writeRow]
      by_cases he : r = q
      · subst r
        simp only [hx.1, ite_false, List.mem_cons, true_or, ite_true]
      · simp only [he, ite_false, List.mem_cons, Ne.symm he, false_or]
  rw [mapRows_eq, Fin.foldl_eq_finRange_foldl, aux _ (List.nodup_finRange rows) a,
    ite_eq_left (List.mem_finRange q)]

/-- Transposition exchanges every packed row's words and bit planes. -/
theorem read_transposeRows (a : Rows rows) (hn : 8 * (rows * 64) < 4294967296) (r : Fin rows) :
    readRow (transposeRows a hn) r = transpose (readRow a r) := read_mapRows a hn transpose r

/-- Applying the row transpose twice recovers every row. -/
theorem read_transposeRows_twice (a : Rows rows) (hn : 8 * (rows * 64) < 4294967296)
    (r : Fin rows) :
    readRow (transposeRows (transposeRows a hn) hn) r = readRow a r := by
  rw [read_transposeRows, read_transposeRows, transpose_transpose]

/-- Transposing packed words establishes the bit-plane representation relation. -/
theorem transposeRows_represents (a : Rows rows) (hn : 8 * (rows * 64) < 4294967296) :
    Represents (transposeRows a hn) a := by
  intro r c
  rw [read_transposeRows]
  simp only [lane, transpose_transpose, readRow, Block.get_ofFn, wordIndex]

/-- Output transposition materializes each decoded lane in place. -/
theorem read_transposeRows_word (a : Rows rows) (hn : 8 * (rows * 64) < 4294967296)
    (r : Fin rows) (c : Fin 64) :
    BF64.Packed.read (transposeRows a hn) (wordIndex r c) = lane (readRow a r) c := by
  have h := congrArg (fun b => b.get c) (read_transposeRows a hn r)
  have hv : (BF64.Packed.read (transposeRows a hn) (wordIndex r c)).val =
      (lane (readRow a r) c).val := by
    simpa only [readRow, Block.get_ofFn, wordIndex, lane] using h
  exact congrArg Word.mk hv

/-- Encode a physical row-major buffer through in-place bit planes. -/
def encode (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) : Rows (2 ^ d) :=
  transposeRows (forward p ell hell (transposeRows a hn) hn) hn

/-- Decode a physical row-major buffer through in-place bit planes. -/
def decode (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) : Rows (2 ^ d) :=
  transposeRows (inverse p ell hell (transposeRows a hn) hn) hn

/-- Encoding agrees in every word with the existing certified packed transform. -/
theorem read_encode (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) (r : Fin (2 ^ d)) (c : Fin 64) :
    BF64.Packed.read (encode p ell hell a hn) (wordIndex r c) =
      BF64.Packed.read (Packed.forward p.toPacked ell hell 64 a) (wordIndex r c) := by
  rw [encode, read_transposeRows_word]
  exact forward_represents p ell hell _ a (transposeRows_represents a hn) hn r c

/-- Decoding agrees in every word with the existing certified packed inverse. -/
theorem read_decode (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) (r : Fin (2 ^ d)) (c : Fin 64) :
    BF64.Packed.read (decode p ell hell a hn) (wordIndex r c) =
      BF64.Packed.read (Packed.inverse p.toPacked ell hell 64 a) (wordIndex r c) := by
  rw [decode, read_transposeRows_word]
  exact inverse_represents p ell hell _ a (transposeRows_represents a hn) hn r c

end AdditiveNTT.Bitsliced
