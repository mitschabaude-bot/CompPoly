/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Univariate.ToPoly.RingHom
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Executable triangular polynomial-basis conversion

Descending elimination computes coordinates in any basis whose `i`-th
polynomial has degree `i`. The reconstruction theorem certifies the ordinary
array-valued conversion without a matrix inverse.
-/

@[expose] public section

namespace CompPoly.CPolynomial

/-- Descending coefficient elimination in a triangular polynomial basis. -/
def triangularBasisCoefficients {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (basis : Nat → CPolynomial F) : Nat → CPolynomial F → Array F
  | 0, _ => #[]
  | n + 1, p =>
    let c := p.coeff n / (basis n).coeff n
    (triangularBasisCoefficients basis n (p - C c * basis n)).push c

/-- Triangular conversion returns one coefficient per basis vector. -/
theorem triangularBasisCoefficients_size {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (basis : Nat → CPolynomial F) (n : Nat) (p : CPolynomial F) :
    (triangularBasisCoefficients basis n p).size = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [triangularBasisCoefficients, Array.size_push, ih]

/-- Cancelling the top coefficient lowers a polynomial's strict degree bound. -/
theorem triangularBasis_remainder_degree_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p b : CPolynomial F} {n : Nat}
    (hp : p.toPoly.degree < (n + 1 : Nat))
    (hb : b.toPoly.degree = (n : Nat)) :
    (p - C (p.coeff n / b.coeff n) * b).toPoly.degree < (n : Nat) := by
  have hbn : b.coeff n ≠ 0 := by
    rw [coeff_toPoly]
    exact Polynomial.coeff_ne_zero_of_eq_degree hb
  rw [Polynomial.degree_lt_iff_coeff_zero] at hp ⊢
  intro i hi
  rw [toPoly_sub, toPoly_mul, C_toPoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  by_cases heq : i = n
  · subst i
    rw [← coeff_toPoly, ← coeff_toPoly, div_mul_cancel₀ _ hbn, sub_self]
  · have hn : n < i := by omega
    rw [hp i (by omega), Polynomial.coeff_eq_zero_of_degree_lt (by simpa [hb] using hn)]
    ring

/-- The computed triangular coordinates reconstruct every degree-bounded input. -/
theorem triangularBasisCoefficients_reconstruct {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (basis : Nat → CPolynomial F) (n : Nat)
    (hbasis : ∀ i, i < n → (basis i).toPoly.degree = (i : Nat))
    (p : CPolynomial F) (hp : p.toPoly.degree < (n : Nat)) :
    ∑ i ∈ Finset.range n,
      Polynomial.C ((triangularBasisCoefficients basis n p).getD i 0) * (basis i).toPoly =
        p.toPoly := by
  induction n generalizing p with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [Polynomial.degree_lt_iff_coeff_zero] at hp
    apply Polynomial.ext
    intro i
    simpa only [Polynomial.coeff_zero] using (hp i (Nat.zero_le i)).symm
  | succ n ih =>
    let c := p.coeff n / (basis n).coeff n
    let rest := p - C c * basis n
    have hrest : rest.toPoly.degree < (n : Nat) :=
      triangularBasis_remainder_degree_lt hp (hbasis n (by omega))
    have hrec := ih (fun i hi ↦ hbasis i (by omega)) rest hrest
    rw [Finset.sum_range_succ]
    have hget (i : Nat) (hi : i < n) :
        (triangularBasisCoefficients basis (n + 1) p).getD i 0 =
          (triangularBasisCoefficients basis n rest).getD i 0 := by
      change ((triangularBasisCoefficients basis n rest).push c).getD i 0 = _
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push,
        triangularBasisCoefficients_size, Nat.ne_of_lt hi, ite_false]
    have hlast : (triangularBasisCoefficients basis (n + 1) p).getD n 0 = c := by
      change ((triangularBasisCoefficients basis n rest).push c).getD n 0 = c
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push,
        triangularBasisCoefficients_size, ite_true, Option.getD_some]

    rw [Finset.sum_congr rfl (fun i hi ↦ congrArg
      (fun x ↦ Polynomial.C x * (basis i).toPoly) (hget i (Finset.mem_range.mp hi))),
      hlast, hrec]
    simp only [rest, toPoly_sub, toPoly_mul, C_toPoly, sub_add_cancel]

end CompPoly.CPolynomial
