/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Transform

/-! # Row and lane indexing of packed additive butterflies -/

@[expose] public section

namespace AdditiveNTT.Packed

/-- Number of rows covered by a stage's disjoint blocks. -/
theorem stage_row_count (d : Nat) (i : Fin d) :
    2 ^ (d - i.val - 1) * (2 * 2 ^ i.val) = 2 ^ d := by
  simpa only [Nat.mul_one] using stage_word_count d i 1

/-- The row partition induced by one additive stage. -/
def rowIndex (d : Nat) (i : Fin d) :
    Fin (2 ^ (d - i.val - 1) * 2 ^ i.val) × Fin 2 ≃ Fin (2 ^ d) :=
  (pairIndex _ _).trans (finCongr (stage_row_count d i))

/-- The flat pair index preserves the row's offset and its lane. -/
theorem stageIndex_lane (d : Nat) (i : Fin d) (lanes : Nat)
    (u : Fin (2 ^ (d - i.val - 1))) (v : Fin (2 ^ i.val))
    (lane : Fin lanes) (b : Fin 2) :
    stageIndex d i lanes (finProdFinEquiv (u, finProdFinEquiv (v, lane)), b) =
      finProdFinEquiv (rowIndex d i (finProdFinEquiv (u, v), b), lane) := by
  apply Fin.ext
  simp only [stageIndex_apply, rowIndex, Equiv.trans_apply, pairIndex,
    Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  simp only [finCongr_apply, Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk]
  ring

/-- The row index written as a natural-number block, side and offset. -/
theorem rowIndex_val (d : Nat) (i : Fin d)
    (u : Fin (2 ^ (d - i.val - 1))) (v : Fin (2 ^ i.val)) (b : Fin 2) :
    (rowIndex d i (finProdFinEquiv (u, v), b)).val =
      v.val + 2 ^ i.val * (b.val + 2 * u.val) := by
  simp only [rowIndex, Equiv.trans_apply, pairIndex,
    Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  simp only [finCongr_apply, Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk]
  ring

/-- Divide a stage row by the butterfly stride. -/
theorem rowIndex_div (d : Nat) (i : Fin d)
    (u : Fin (2 ^ (d - i.val - 1))) (v : Fin (2 ^ i.val)) (b : Fin 2) :
    (rowIndex d i (finProdFinEquiv (u, v), b)).val / 2 ^ i.val =
      b.val + 2 * u.val := by
  rw [rowIndex_val, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt v.isLt, Nat.zero_add]

/-- The lower row plus the stride is its paired upper row. -/
theorem rowIndex_one (d : Nat) (i : Fin d)
    (u : Fin (2 ^ (d - i.val - 1))) (v : Fin (2 ^ i.val)) :
    (rowIndex d i (finProdFinEquiv (u, v), 1)).val =
      (rowIndex d i (finProdFinEquiv (u, v), 0)).val + 2 ^ i.val := by
  rw [rowIndex_val, rowIndex_val]
  simp only [Fin.val_one, Fin.val_zero]
  ring

/-- XOR at the stride bit takes an upper row to its paired lower row. -/
theorem rowIndex_xor (d : Nat) (i : Fin d)
    (u : Fin (2 ^ (d - i.val - 1))) (v : Fin (2 ^ i.val)) :
    (rowIndex d i (finProdFinEquiv (u, v), 1)).val ^^^ 2 ^ i.val =
      (rowIndex d i (finProdFinEquiv (u, v), 0)).val := by
  have hb : Nat.getBit i.val (rowIndex d i (finProdFinEquiv (u, v), 1)).val = 1 := by
    simp only [Nat.getBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, rowIndex_div]
    omega
  rw [(Nat.xor_eq_sub_iff_submask (by rw [rowIndex_one]; omega)).mpr
    (Nat.and_two_pow_eq_two_pow_of_getBit_1 hb), rowIndex_one, Nat.add_sub_cancel]

end AdditiveNTT.Packed
