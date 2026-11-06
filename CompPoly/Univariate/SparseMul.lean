/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import all CompPoly.Univariate.Basic
public import CompPoly.Univariate.Context

/-! # Polynomial multiplication omitting zero coefficient rows -/

@[expose] public section

namespace CompPoly.CPolynomial

/-- Convolution with zero rows omitted and a single final canonicalization. -/
def mulSkipZeros {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) : CPolynomial R :=
  let raw := p.val.zipIdx.foldl (fun acc (a, i) ↦
    if a == 0 then acc else Raw.addRaw acc ((Raw.smul a q.val).mulPowX i)) (Raw.mk #[])
  ⟨raw.trim, Raw.Trim.isCanonical_trim raw⟩

private theorem foldSkipZeros_coeff {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]
    (q : Raw R) (xs : List (R × Nat)) (a b : Raw R)
    (h : ∀ k, a.coeff k = b.coeff k) :
    ∀ k, (xs.foldl (fun acc (c, i) ↦
      if c == 0 then acc else Raw.addRaw acc ((Raw.smul c q).mulPowX i)) a).coeff k =
      (xs.foldl (fun acc (c, i) ↦
        Raw.addRaw acc ((Raw.smul c q).mulPowX i)) b).coeff k := by
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro k
    by_cases hz : x.1 == 0
    · have hc : x.1 = 0 := eq_of_beq hz
      simp only [hc, beq_self_eq_true, ite_true, Raw.add_coeff?, Raw.coeff_mulPowX,
        Raw.smul_equiv, MulZeroClass.zero_mul, ite_self, _root_.add_zero, h]
    · simp only [hz, Bool.false_eq_true, ite_false, Raw.add_coeff?, h]

/-- Omitting zero rows preserves canonical polynomial multiplication. -/
theorem mulSkipZeros_eq_mul {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) : mulSkipZeros p q = p * q := by
  apply Subtype.ext
  change _ = Raw.mul p.val q.val
  unfold mulSkipZeros Raw.mul Raw.mulRaw
  apply Raw.Trim.eq_of_equiv
  intro k
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldSkipZeros_coeff q.val _ _ _ (fun _ ↦ rfl) k

/-- Multiplication context for operands whose first coefficient array is sparse. -/
def MulContext.skipZeros {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] : MulContext R where
  mul := mulSkipZeros
  mul_eq_mul := mulSkipZeros_eq_mul

end CompPoly.CPolynomial
