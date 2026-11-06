/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Univariate.Roots.Shoup.Basic
public import Mathlib.FieldTheory.Finite.Trace

/-!
# Binary trace contexts from spanning arrays

An explicit array spanning a finite binary field supplies the separating trace
coordinates required by the deterministic Shoup splitter. Field cardinality,
trace nondegeneracy, and spanning are used only in the proofs; no field
enumeration is part of the executable context.
-/

@[expose] public section

namespace CompPoly.CPolynomial.Roots.FiniteField

/-- Cardinality determines the binary dimension without enumerating the field. -/
theorem binary_finrank_of_card {F : Type*} [Field F] [Finite F]
    [Algebra (ZMod 2) F] {k : Nat} (hcard : Nat.card F = 2 ^ k) :
    Module.finrank (ZMod 2) F = k := by
  classical
  let := Fintype.ofFinite F
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  change 2 ^ Module.finrank (ZMod 2) F = 2 ^ k
  rw [← hcard, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- The binary power sum is the field trace, embedded back into the extension. -/
theorem tracePowerSum_eq_binary_trace {F : Type*} [Field F] [Finite F]
    [Algebra (ZMod 2) F] {k : Nat} (hcard : Nat.card F = 2 ^ k) (z : F) :
    tracePowerSum 2 k z = algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) F z) := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, binary_finrank_of_card hcard,
    tracePowerSum_eq_sum_range]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

/-- Binary traces take values in the explicit two-element prime-field array. -/
theorem tracePowerSum_mem_binary_base {F : Type*} [Field F] [Finite F]
    [Algebra (ZMod 2) F] {k : Nat} (hcard : Nat.card F = 2 ^ k) (z : F) :
    tracePowerSum 2 k z ∈ (#[0, 1] : Array F).toList := by
  rw [tracePowerSum_eq_binary_trace hcard]
  have h : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h (Algebra.trace (ZMod 2) F z) with hz | hz <;>
    simp only [hz, map_zero, map_one, List.mem_cons, List.not_mem_nil,
      or_false, eq_self, true_or, or_true]

/-- A spanning array separates nonzero differences under the binary trace pairing. -/
theorem tracePowerSum_separates_of_span {F : Type*} [Field F] [Finite F]
    [Algebra (ZMod 2) F] {k : Nat} (hcard : Nat.card F = 2 ^ k)
    (basis : Array F) (hspan : Submodule.span (ZMod 2) {x | x ∈ basis.toList} = ⊤)
    {d : F} (hd : d ≠ 0) :
    ∃ beta, beta ∈ basis.toList ∧ tracePowerSum 2 k (beta * d) ≠ 0 := by
  classical
  by_contra! h
  have hker : Submodule.span (ZMod 2) {x | x ∈ basis.toList} ≤
      LinearMap.ker (Algebra.traceForm (ZMod 2) F d) := by
    apply Submodule.span_le.mpr
    intro x hx
    have hz := h x hx
    rw [tracePowerSum_eq_binary_trace hcard, mul_comm] at hz
    change Algebra.trace (ZMod 2) F (d * x) = 0
    exact (FaithfulSMul.algebraMap_injective (ZMod 2) F)
      (by simpa only [map_zero] using hz)
  rw [hspan, top_le_iff] at hker
  have hz : ∀ v, Algebra.trace (ZMod 2) F (d * v) = 0 := by
    intro v
    change v ∈ LinearMap.ker (Algebra.traceForm (ZMod 2) F d)
    rw [hker]
    trivial
  exact hd ((traceForm_nondegenerate (ZMod 2) F).1 d hz)

/-- Deterministic binary-field trace context from explicit spanning coordinates. -/
def binaryTraceContextOfSpan {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [Finite F] [Algebra (ZMod 2) F]
    (k : Nat) (hcard : Nat.card F = 2 ^ k)
    (basis : Array F) (hsize : basis.size = k)
    (hspan : Submodule.span (ZMod 2) {x | x ∈ basis.toList} = ⊤) :
    SmallPrimeTraceContext F where
  q := 2 ^ k
  finite := inferInstance
  card_eq := hcard
  frobenius_fixed := by
    classical
    let := Fintype.ofFinite F
    intro a
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  p := 2
  k := k
  p_prime := Nat.prime_two
  q_eq := rfl
  baseConstants := #[0, 1]
  baseConstants_size := rfl
  basis := basis
  basis_size := hsize
  traceValue := tracePowerSum 2 k
  traceValue_eq_powerSum := fun _ ↦ rfl
  traceValue_mem_base := tracePowerSum_mem_binary_base hcard
  trace_separates := fun h ↦ tracePowerSum_separates_of_span hcard basis hspan (sub_ne_zero.mpr h)

end CompPoly.CPolynomial.Roots.FiniteField
