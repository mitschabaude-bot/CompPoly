/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import all CompPoly.Univariate.Basic
public import CompPoly.Univariate.ReedSolomon.GaoNTT
public import CompPoly.Univariate.BatchEval.Interpolation
public import CompPoly.Univariate.Vanishing

/-! # Gao decoding with certified subproduct-tree inputs -/

@[expose] public section

namespace CompPoly.ReedSolomon.Gao

open CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The Euclidean stage with direct handling of the unit error locator. -/
def decodeFromUnit (k n : Nat) (G R : CPolynomial F) : Option (CPolynomial F) :=
  let (g, _, v) := CPolynomial.xgcd G R ((n + k + 1) / 2)
  if v == 1 then
    if g.degree < k then some g else none
  else if g.mod v == 0 then
    let f := g / v
    if f.degree < k then some f else none
  else none

/-- A unit locator requires no polynomial division. -/
@[csimp] theorem decodeFrom_eq_decodeFromUnit : @decodeFrom = @decodeFromUnit := by
  funext F _ _ _ k n G R
  have hdiv (p : CPolynomial F) : p / 1 = p := by
    apply CPolynomial.toPoly_injective
    change (CPolynomial.div p 1).toPoly = p.toPoly
    rw [CPolynomial.div_toPoly_eq_div, CPolynomial.toPoly_one, EuclideanDomain.div_one]
  have hmod (p : CPolynomial F) : p.mod 1 = 0 := by
    apply CPolynomial.toPoly_injective
    rw [CPolynomial.mod_toPoly_eq_smul_mod, CPolynomial.toPoly_one,
      EuclideanDomain.mod_one, smul_zero, CPolynomial.toPoly_zero]
  unfold decodeFrom decodeFromUnit
  generalize CPolynomial.xgcd G R ((n + k + 1) / 2) = triple
  rcases triple with ⟨g, u, v⟩
  dsimp only
  by_cases hv : v == 1
  · have heq := eq_of_beq hv
    simp only [heq, hdiv, hmod, beq_self_eq_true, ↓reduceIte]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]

/-- Gao decoding with tree interpolation and a certified nodal-polynomial context. -/
def decodeTree (M : MulContext F) (V : VanishingPolynomialContext F)
    (k : Nat) (D : Domain F) (r : Vector F D.n) : Option (CPolynomial F) :=
  decodeFrom k D.n (V.vanishingPolynomial D.val)
    (interpolateSubproduct M ModContext.remainderOnly D.val r.toArray)

/-- The folded nodal polynomial is the array vanishing polynomial. -/
theorem nodalPoly_eq_vanishing (D : Domain F) :
    nodalPoly D = vanishingPolynomialArray D.val := by
  unfold nodalPoly vanishingPolynomialArray
  congr 1
  funext acc x
  congr 1
  apply toPoly_injective
  simp only [linearFactor, toPoly_sub, toPoly_add, C_toPoly, X_toPoly, Polynomial.C_neg]
  ring

/-- Tree interpolation is Gao's received interpolant. -/
theorem interpolateSubproduct_eq_receivedInterpolant (M : MulContext F)
    (D : Domain F) (r : Vector F D.n) :
    interpolateSubproduct M ModContext.remainderOnly D.val r.toArray =
      receivedInterpolant D r := by
  rw [interpolateSubproduct_eq_interpolateArrays M _ _ _ D.property]
  unfold CLagrange.interpolateArrays receivedInterpolant
  congr 1
  funext i
  have hi : i.val < r.toArray.size := by simpa only [Vector.size_toArray] using i.isLt
  simp only [CLagrange.arrayValue, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hi, Option.getD_some, Vector.get]
  rfl

/-- The tree implementation agrees with the decoder used by Gao correctness. -/
theorem decodeTree_eq_decode (M : MulContext F) (V : VanishingPolynomialContext F)
    (k : Nat) (D : Domain F) (r : Vector F D.n) :
    decodeTree M V k D r = decode k D r := by
  rw [decodeTree, V.correct, ← nodalPoly_eq_vanishing,
    interpolateSubproduct_eq_receivedInterpolant, decode_eq_decodeFrom]

end CompPoly.ReedSolomon.Gao
