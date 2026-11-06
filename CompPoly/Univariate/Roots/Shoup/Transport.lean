/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Univariate.Roots.Shoup.Basic

/-! # Trace contexts across executable field isomorphisms -/

@[expose] public section

namespace CompPoly.CPolynomial.Roots.FiniteField

/-- Transport a separating trace basis without constructing a field enumeration. -/
def SmallPrimeTraceContext.map {F K : Type*} [Field F] [Field K]
    [BEq F] [LawfulBEq F] [BEq K] [LawfulBEq K]
    (ctx : SmallPrimeTraceContext F) (e : F ≃+* K) : SmallPrimeTraceContext K where
  q := ctx.q
  finite := by
    let : Finite F := ctx.finite
    exact Finite.of_equiv F e.toEquiv
  card_eq := (Nat.card_congr e.toEquiv).symm.trans ctx.card_eq
  frobenius_fixed a := by
    apply e.symm.injective
    rw [map_pow, ctx.frobenius_fixed]
  p := ctx.p
  k := ctx.k
  p_prime := ctx.p_prime
  q_eq := ctx.q_eq
  baseConstants := ctx.baseConstants.map e
  baseConstants_size := by rw [Array.size_map, ctx.baseConstants_size]
  basis := ctx.basis.map e
  basis_size := by rw [Array.size_map, ctx.basis_size]
  traceValue a := e (ctx.traceValue (e.symm a))
  traceValue_eq_powerSum a := by
    rw [ctx.traceValue_eq_powerSum, tracePowerSum_eq_sum_range,
      tracePowerSum_eq_sum_range, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_pow, RingEquiv.apply_symm_apply]
  traceValue_mem_base a := by
    rw [Array.toList_map, List.mem_map]
    exact ⟨_, ctx.traceValue_mem_base _, rfl⟩
  trace_separates := by
    intro a b hab
    obtain ⟨beta, hb, ht⟩ := ctx.trace_separates (fun h ↦ hab (e.symm.injective h))
    refine ⟨e beta, ?_, ?_⟩
    · rw [Array.toList_map, List.mem_map]
      exact ⟨beta, hb, rfl⟩
    · rw [map_mul, map_sub, RingEquiv.symm_apply_apply]
      exact fun hz ↦ ht (e.injective (hz.trans (map_zero e).symm))

end CompPoly.CPolynomial.Roots.FiniteField
