/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import all CompPoly.Univariate.CoefficientInterpolation
public import CompPoly.Univariate.CoefficientInterpolation
public import CompPoly.Univariate.BatchEval.Interpolation
public import CompPoly.Univariate.SparseMul

/-! # Tree assembly of the coefficient-form interpolant -/

@[expose] public section

namespace CompPoly.CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The coefficient-form interpolant has degree below the number of nodes. -/
theorem interpolateCoefficientForm_degree_lt
    (V : VanishingPolynomialContext F) (E : BatchEvalContext F)
    (points : Array (F × F)) :
    (interpolateCoefficientForm V E points).degree < points.size := by
  let G := V.vanishingPolynomial (points.map Prod.fst)
  have hnat : G.val.size - 1 = points.size := by
    have hn := natDegree_toPoly G
    change G.val.size - 1 = G.toPoly.natDegree at hn
    rw [hn]
    dsimp only [G]
    rw [V.correct, vanishingPolynomialArray_toPoly,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
    simp only [Multiset.coe_card, Array.length_toList, Array.size_map]
  have hterm (point : F × F) (d : F) :
      (interpolationTermWithVanishing G point d).degree < points.size := by
    rw [degree_lt_iff_coeff_zero]
    intro i hi
    rw [coeff_toPoly, interpolationTermWithVanishing, toPoly_mul, C_toPoly,
      Polynomial.coeff_C_mul, ← coeff_toPoly,
      divByLinearFactor_coeff_eq_zero_of_le G point.1 (hnat ▸ hi), MulZeroClass.mul_zero]
  have hfold (is : List Nat) (acc : CPolynomial F) (ha : acc.degree < points.size)
      (values : Array F) :
      (is.foldl (fun acc i ↦ acc + interpolationTermWithVanishing G
        (points.getD i (0, 0)) (values.getD i 0)) acc).degree < points.size := by
    induction is generalizing acc with
    | nil => exact ha
    | cons i is ih =>
      apply ih
      rw [degree_toPoly, toPoly_add]
      apply lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact degree_toPoly acc ▸ ha
      · simpa only [degree_toPoly] using
          hterm (points.getD i (0, 0)) (values.getD i 0)
  exact hfold _ 0 (by simp only [degree_zero]; exact WithBot.bot_lt_coe _) _

/-- Distinct packed-node coefficient interpolation is array Lagrange interpolation. -/
theorem interpolateCoefficientForm_eq_interpolateArrays [DecidableEq F]
    (V : VanishingPolynomialContext F) (E : BatchEvalContext F)
    (points : Array (F × F)) (hd : (points.toList.map Prod.fst).Nodup) :
    interpolateCoefficientForm V E points =
      CLagrange.interpolateArrays (points.map Prod.fst) (points.map Prod.snd) := by
  apply toPoly_injective
  rw [CLagrange.interpolateArrays, CLagrange.cinterpolate_eq_interpolate]
  have hinj : Set.InjOn (CLagrange.arrayNode (points.map Prod.fst))
      (↑(Finset.univ : Finset (Fin (points.map Prod.fst).size))) := by
    intro i _ j _ hij
    apply Fin.ext
    exact (List.Nodup.getElem_inj (by simpa only [Array.toList_map] using hd)).mp hij
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := Finset.univ)
    (v := CLagrange.arrayNode (points.map Prod.fst)) hinj ?_ ?_ ?_
  · simpa only [Finset.card_univ, Fintype.card_fin, Array.size_map, ← degree_toPoly] using
      interpolateCoefficientForm_degree_lt V E points
  · exact Lagrange.degree_interpolate_lt _ hinj
  · intro i _
    rw [Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)]
    have hi : i.val < points.size := by simpa only [Array.size_map] using i.isLt
    change _ = (points.map Prod.snd).getD i.val 0
    rw [show (CLagrange.arrayNode (points.map Prod.fst) i) = points[i.val].1 from
      Array.getElem_map ..]
    simpa only [CLagrange.arrayNode, CLagrange.arrayValue, Array.getElem_map,
      Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some, ← eval_toPoly] using
      interpolateCoefficientForm_eval_point V E hd (Array.getElem_mem_toList hi)

/-- Assemble distinct-node interpolants through a subproduct tree. -/
def interpolateCoefficientFormTree
    (V : VanishingPolynomialContext F) (E : BatchEvalContext F)
    (points : Array (F × F)) : CPolynomial F :=
  letI : DecidableEq F := fun a b ↦ decidable_of_iff ((a == b) = true) beq_iff_eq
  let xs := points.map Prod.fst
  if xs.toList.Nodup then
    interpolateSubproduct MulContext.skipZeros ModContext.remainderOnly xs (points.map Prod.snd)
  else interpolateCoefficientFormWithVanishing E
    (V.vanishingPolynomial (points.map Prod.fst)) points

/-- Tree assembly preserves the coefficient-form specification on every input. -/
@[csimp] theorem interpolateCoefficientFormTree_eq :
    @interpolateCoefficientForm = @interpolateCoefficientFormTree := by
  funext F _ _ _ V E points
  let : DecidableEq F := fun a b ↦ decidable_of_iff ((a == b) = true) beq_iff_eq
  unfold interpolateCoefficientFormTree
  dsimp only
  split
  · rename_i h
    rw [interpolateSubproduct_eq_interpolateArrays _ _ _ _ h]
    exact interpolateCoefficientForm_eq_interpolateArrays V E points (by
      simpa only [Array.toList_map] using h)
  · rfl

end CompPoly.CPolynomial
