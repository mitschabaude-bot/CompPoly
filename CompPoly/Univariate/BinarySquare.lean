/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Univariate.ToPoly.Degree
public import CompPoly.Univariate.ToPoly.RingHom
public import Mathlib.Algebra.Polynomial.Expand

/-! # Coefficientwise squaring in characteristic two -/

@[expose] public section

namespace CompPoly.CPolynomial

/-- Square coefficients and double their exponents, leaving odd coefficients zero. -/
def binarySquare {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : CPolynomial F :=
  ofFn fun i : Fin (2 * p.val.size) ↦
    if 2 ∣ i.val then p.coeff (i.val / 2) * p.coeff (i.val / 2) else 0

/-- In characteristic two, exponent dilation is the ordinary polynomial square. -/
theorem binarySquare_eq_mul_self {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [CharP F 2] (p : CPolynomial F) : binarySquare p = p * p := by
  apply toPoly_injective
  rw [toPoly_mul, ← sq, ← Polynomial.map_frobenius_expand 2]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_expand (by decide), ← coeff_toPoly]
  unfold binarySquare
  rw [coeff_ofFn]
  by_cases hi : i < 2 * p.val.size
  · simp only [hi, dite_true]
    split_ifs <;> simp only [← coeff_toPoly, frobenius_def, sq, map_zero]
  · have hz : p.coeff (i / 2) = 0 := coeff_eq_zero_of_size_le p (by omega)
    simp only [hi, dite_false, ← coeff_toPoly, hz, ite_self, map_zero]

end CompPoly.CPolynomial
