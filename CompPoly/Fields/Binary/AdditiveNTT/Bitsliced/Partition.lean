/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Transform
public import Mathlib.Data.List.Nodup
/-! # Disjoint row pairs of an additive stage -/
@[expose] public section
namespace AdditiveNTT.Bitsliced

/-- A stage's block index and offset within its half-block. -/
abbrev PairIndex (d : Nat) (i : Fin d) := Fin (2 ^ (d - i.val - 1)) × Fin (2 ^ i.val)

/-- The row-pair partition inherited from the certified packed transform. -/
def rowPartition (d : Nat) (i : Fin d) : PairIndex d i × Fin 2 ≃ Fin (2 ^ d) :=
  (Equiv.prodCongr
    ((finProdFinEquiv : Fin (2 ^ (d - i.val - 1)) × Fin (2 ^ i.val) ≃ _).trans
      (finCongr (by simp only [Nat.mul_one]))) (Equiv.refl _)).trans
    ((Packed.stageIndex d i 1).trans (finCongr (Nat.mul_one _)))

/-- The row partition's address is its block, side and in-block offset. -/
theorem rowPartition_val (d : Nat) (i : Fin d) (j : PairIndex d i) (b : Fin 2) :
    (rowPartition d i (j, b)).val =
      (j.1.val * (2 * 2 ^ i.val) + j.2.val) + 2 ^ i.val * b.val := by
  have hs : 0 < 2 ^ i.val := by positivity
  change (j.2.val + 2 ^ i.val * j.1.val) % (2 ^ i.val * 1) +
    (2 ^ i.val * 1) * b.val + (2 * (2 ^ i.val * 1)) *
      ((j.2.val + 2 ^ i.val * j.1.val) / (2 ^ i.val * 1)) = _
  rw [Nat.mul_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.2.isLt,
    Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt j.2.isLt]
  ring

/-- Every stage visits every pair exactly once. -/
def pairList (d : Nat) (i : Fin d) : List (PairIndex d i) :=
  (List.finRange (2 ^ (d - i.val - 1))).product (List.finRange (2 ^ i.val))

/-- Stage pairs are distinct. -/
theorem pairList_nodup (d : Nat) (i : Fin d) : (pairList d i).Nodup :=
  (List.nodup_finRange _).product (List.nodup_finRange _)

/-- Each pair occurs in its stage's sweep. -/
theorem mem_pairList (d : Nat) (i : Fin d) (j : PairIndex d i) : j ∈ pairList d i := by
  exact List.mem_product.mpr ⟨List.mem_finRange j.1, List.mem_finRange j.2⟩

end AdditiveNTT.Bitsliced
