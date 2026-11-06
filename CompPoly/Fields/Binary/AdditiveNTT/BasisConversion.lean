/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import all CompPoly.Univariate.Basic
public import CompPoly.Univariate.Basis.Triangular
public import CompPoly.Fields.Binary.AdditiveNTT.Correctness

/-!
# Executable monomial-to-novel conversion

Explicit binary subspace products construct the normalized novel basis.
Descending triangular elimination computes its coefficients and certifies
agreement with the mathematical novel polynomial basis.
-/

@[expose] public section

namespace AdditiveNTT

open CompPoly

/-- Binary subspace element with the little-endian coordinate mask `mask`. -/
def subspaceMaskValue {F : Type*} [AddCommMonoid F] {r : Nat}
    (β : Fin r → F) (i : Fin r) (mask : Nat) : F :=
  ∑ j : Fin i.val, if Nat.getBit j.val mask == 1 then β ⟨j.val, by omega⟩ else 0

/-- Executable vanishing polynomial of a binary coordinate subspace. -/
def subspacePolynomial {F : Type*} [Field F] [BEq F] [LawfulBEq F] {r : Nat}
    (β : Fin r → F) (i : Fin r) : CPolynomial F :=
  ∏ mask : Fin (2 ^ i.val), CPolynomial.linearFactor (subspaceMaskValue β i mask.val)

/-- Executable normalized binary subspace polynomial. -/
def normalizedSubspacePolynomial {F : Type*} [Field F] [BEq F] [LawfulBEq F] {r : Nat}
    (β : Fin r → F) (i : Fin r) : CPolynomial F :=
  let W := subspacePolynomial β i
  CPolynomial.C (CPolynomial.eval (β i) W)⁻¹ * W

/-- Cache the normalized subspace polynomials used by a novel basis. -/
def normalizedSubspacePolynomials {F : Type*} [Field F] [BEq F] [LawfulBEq F] {r : Nat}
    (β : Fin r → F) (ℓ : Nat) (hℓ : ℓ ≤ r) : Array (CPolynomial F) :=
  Array.ofFn fun i : Fin ℓ ↦ normalizedSubspacePolynomial β (Fin.castLE hℓ i)

/-- A novel basis polynomial obtained from cached normalized subspace factors. -/
def novelBasisPolynomial {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (normalized : Array (CPolynomial F)) (ℓ index : Nat) : CPolynomial F :=
  ∏ i : Fin ℓ, (normalized.getD i.val 0) ^ (Nat.getBit i.val index)

/-- Convert canonical monomial coefficients to a full array of novel coefficients. -/
def monomialToNovelArray {F : Type*} [Field F] [BEq F] [LawfulBEq F] {r : Nat}
    (β : Fin r → F) (ℓ : Nat) (hℓ : ℓ ≤ r) (p : CPolynomial F) : Array F :=
  let normalized := normalizedSubspacePolynomials β ℓ hℓ
  CPolynomial.triangularBasisCoefficients (novelBasisPolynomial normalized ℓ) (2 ^ ℓ) p

section Correctness

variable {r : Nat} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [BEq L] [LawfulBEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [Algebra 𝔽q L]
variable [Fact (Fintype.card 𝔽q = 2)]
variable (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)]

/-- The executable subspace product represents the mathematical subspace polynomial. -/
theorem subspacePolynomial_toPoly (i : Fin r) :
    (subspacePolynomial β i).toPoly = W 𝔽q β i := by
  classical
  rw [subspacePolynomial, CPolynomial.toPoly_prod, W]
  apply Finset.prod_bij
    (fun k _ ↦ bitsToU (𝔽q := 𝔽q) (β := β) (ℓ := 0) (R_rate := 0) i k)
  · intro k _
    exact Finset.mem_univ _
  · intro k _ k' _ heq
    exact (bitsToU_bijective (𝔽q := 𝔽q) (β := β) (ℓ := 0) (R_rate := 0) i).1 heq
  · intro v _
    obtain ⟨k, hk⟩ :=
      (bitsToU_bijective (𝔽q := 𝔽q) (β := β) (ℓ := 0) (R_rate := 0) i).2 v
    exact ⟨k, Finset.mem_univ _, hk⟩
  · intro k _
    rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.X_toPoly,
      CPolynomial.C_toPoly, Polynomial.C_neg, sub_eq_add_neg]
    exact add_comm _ _

/-- Executable normalization agrees with the normalized subspace specification. -/
theorem normalizedSubspacePolynomial_toPoly (i : Fin r) :
    (normalizedSubspacePolynomial β i).toPoly = normalizedW 𝔽q β i := by
  rw [normalizedSubspacePolynomial, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
    subspacePolynomial_toPoly 𝔽q β, normalizedW]
  congr 2
  rw [CPolynomial.eval_toPoly, subspacePolynomial_toPoly 𝔽q β, one_div]

/-- The cached product represents exactly the mathematical novel basis vector. -/
theorem novelBasisPolynomial_toPoly (ℓ : Nat) (hℓ : ℓ ≤ r) (j : Fin (2 ^ ℓ)) :
    (novelBasisPolynomial (normalizedSubspacePolynomials β ℓ hℓ) ℓ j.val).toPoly =
      Xⱼ 𝔽q β ℓ hℓ j := by
  unfold novelBasisPolynomial normalizedSubspacePolynomials
  rw [CPolynomial.toPoly_prod]
  simp only [CPolynomial.toPoly_pow]
  change (∏ i : Fin ℓ, ((Array.ofFn fun i : Fin ℓ ↦
    normalizedSubspacePolynomial β (Fin.castLE hℓ i)).getD i.val 0).toPoly ^
      Nat.getBit i.val j.val) = _
  apply Finset.prod_congr rfl
  intro i _
  have hget : (Array.ofFn fun i : Fin ℓ ↦
      normalizedSubspacePolynomial β (Fin.castLE hℓ i)).getD i.val 0 =
        normalizedSubspacePolynomial β (Fin.castLE hℓ i) := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      i.isLt, dite_true, Option.getD_some]
  rw [hget, normalizedSubspacePolynomial_toPoly 𝔽q β]

/-- The executable conversion reconstructs the input polynomial in the novel basis. -/
theorem monomialToNovelArray_reconstruct (ℓ : Nat) (hℓ : ℓ ≤ r)
    (p : CPolynomial L) (hp : p.toPoly.degree < (2 ^ ℓ : Nat)) :
    ∑ j : Fin (2 ^ ℓ),
      Polynomial.C ((monomialToNovelArray β ℓ hℓ p).getD j.val 0) *
        Xⱼ 𝔽q β ℓ hℓ j = p.toPoly := by
  have hb (i : Nat) (hi : i < 2 ^ ℓ) :
      (novelBasisPolynomial (normalizedSubspacePolynomials β ℓ hℓ) ℓ i).toPoly.degree =
        (i : Nat) := by
    rw [novelBasisPolynomial_toPoly 𝔽q β ℓ hℓ ⟨i, hi⟩]
    exact degree_Xⱼ 𝔽q β ℓ hℓ ⟨i, hi⟩
  have hrec := CPolynomial.triangularBasisCoefficients_reconstruct
    (novelBasisPolynomial (normalizedSubspacePolynomials β ℓ hℓ) ℓ) (2 ^ ℓ) hb p hp
  rw [Finset.sum_range] at hrec
  simpa only [monomialToNovelArray, novelBasisPolynomial_toPoly 𝔽q β] using hrec

/-- The computed array gives the coordinates of the mathematical novel-basis equivalence. -/
theorem monomialToNovelArray_eq_equivFun (ℓ : Nat) (hℓ : ℓ ≤ r)
    (p : CPolynomial L) (hp : p.toPoly.degree < (2 ^ ℓ : Nat)) :
    (fun j : Fin (2 ^ ℓ) ↦ (monomialToNovelArray β ℓ hℓ p).getD j.val 0) =
      (novelPolynomialBasis 𝔽q β ℓ hℓ).equivFun
        ⟨p.toPoly, Polynomial.mem_degreeLT.mpr hp⟩ := by
  apply (novelPolynomialBasis 𝔽q β ℓ hℓ).equivFun.symm.injective
  rw [Module.Basis.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul,
    novelPolynomialBasis_is_basisVectors, basisVectors, Polynomial.smul_eq_C_mul]
  exact monomialToNovelArray_reconstruct 𝔽q β ℓ hℓ p hp

end Correctness

end AdditiveNTT
