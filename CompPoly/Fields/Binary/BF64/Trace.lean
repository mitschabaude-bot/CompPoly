/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.Ext3
public import CompPoly.Univariate.Roots.Shoup.BinaryTrace
public import CompPoly.Univariate.Roots.Shoup.Correctness
public import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Deterministic root finding over BF64 and its cubic extension

Polynomial-basis bit arrays give 64 and 192 separating binary trace
coordinates. The certified Shoup splitter uses these coordinates without
constructing an enumeration of either field.
-/

@[expose] public section

namespace BF64

open CompPoly.CPolynomial.Roots.FiniteField CompPoly.Extension

/-- The polynomial-basis bit at index `i`. -/
def binaryBasisVector (i : Fin 64) : BF64 := ofBitVec (1 <<< i.val)

/-- Explicit binary coordinates of the polynomial-basis field. -/
def binaryBasis : Array BF64 := Array.ofFn binaryBasisVector

/-- Every field word is the sum of the basis bits present in its representation. -/
theorem eq_sum_binaryBasisVector (a : BF64) :
    a = ∑ i : Fin 64, if a.toBitVec.getLsb i then binaryBasisVector i else 0 := by
  classical
  let f : BF64 →+ BF64Quot :=
    { toFun := toQuot, map_zero' := toQuot_zero, map_add' := toQuot_add }
  apply toQuot_injective
  change f a = f _
  rw [map_sum]
  change AdjoinRoot.mk basePoly (BinaryField.toPoly a.toBitVec) = _
  rw [BinaryField.toPoly, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split
  · change AdjoinRoot.mk basePoly (Polynomial.X ^ i.val) =
      toQuot (binaryBasisVector i)
    rw [toQuot, toPolyBF64, binaryBasisVector, toBitVec_ofBitVec,
      BinaryField.toPoly_one_shiftLeft i.val i.isLt]
  · simp only [map_zero]

/-- Polynomial-basis bits span BF64 over its binary prime field. -/
theorem binaryBasis_span [Algebra (ZMod 2) BF64] :
    Submodule.span (ZMod 2) {x | x ∈ binaryBasis.toList} = ⊤ := by
  apply top_unique
  intro a _
  rw [eq_sum_binaryBasisVector a]
  apply Submodule.sum_mem
  intro i _
  split
  · apply Submodule.subset_span
    simp only [binaryBasis, Array.toList_ofFn, List.mem_ofFn]
    exact ⟨i, rfl⟩
  · exact Submodule.zero_mem _

/-- The explicit polynomial-basis coordinates are linearly independent. -/
theorem binaryBasisVector_linearIndependent [Algebra (ZMod 2) BF64] :
    LinearIndependent (ZMod 2) binaryBasisVector := by
  have hset : {x | x ∈ binaryBasis.toList} = Set.range binaryBasisVector := by
    ext x
    simp only [binaryBasis, Array.toList_ofFn, List.mem_ofFn, Set.mem_ofPred_eq,
      Set.mem_range]
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [← hset, binaryBasis_span]
  · rw [Fintype.card_fin, binary_finrank_of_card nat_card_bf64]

/-- BF64's certified deterministic trace-splitting context. -/
def smallPrimeTraceContext : SmallPrimeTraceContext BF64 := by
  letI := ZMod.algebra BF64 2
  exact binaryTraceContextOfSpan 64 nat_card_bf64 binaryBasis (Array.size_ofFn ..)
    binaryBasis_span

/-- The tensor-product binary coordinate at index `i` of the cubic extension. -/
def ext3BinaryBasisVector (i : Fin 192) : Ext3 :=
  Ext.ofBase (binaryBasisVector ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩) *
    ext3Gen ^ (i.val / 64)

/-- Explicit binary coordinates of the cubic extension, grouped by coefficient limb. -/
def ext3BinaryBasis : Array Ext3 := Array.ofFn ext3BinaryBasisVector

/-- Every cubic-extension element is its three-term coefficient expansion. -/
theorem ext3_eq_sum_coeff (a : Ext3) :
    a = ∑ j : Fin 3, Ext.ofBase (Ext.coeff a j) * ext3Gen ^ j.val := by
  apply Ext.toQuot_injective
  rw [Ext.toQuot_sum]
  simp only [Ext.toQuot_mul, Ext.toQuot_ofBase, Ext.toQuot_pow, toQuot_ext3Gen]
  rfl

/-- Tensor-product binary coordinates span the cubic extension. -/
theorem ext3BinaryBasis_span [Algebra (ZMod 2) Ext3] :
    Submodule.span (ZMod 2) {x | x ∈ ext3BinaryBasis.toList} = ⊤ := by
  apply top_unique
  intro a _
  rw [ext3_eq_sum_coeff a]
  apply Submodule.sum_mem
  intro j _
  rw [eq_sum_binaryBasisVector (Ext.coeff a j)]
  change (Ext.ofBaseRingHom ext3Params) _ * _ ∈ _
  rw [map_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro i _
  split
  · apply Submodule.subset_span
    have hj : j.val * 64 + i.val < 192 := by omega
    have hmod : (j.val * 64 + i.val) % 64 = i.val := by omega
    have hdiv : (j.val * 64 + i.val) / 64 = j.val := by omega
    simp only [ext3BinaryBasis, Array.toList_ofFn, List.mem_ofFn]
    refine ⟨⟨j.val * 64 + i.val, hj⟩, ?_⟩
    simp only [ext3BinaryBasisVector, hmod, hdiv, Ext.ofBaseRingHom_apply]
  · simp only [map_zero, zero_mul]
    exact Submodule.zero_mem _

/-- The explicit tensor-product coordinates are linearly independent over the binary field. -/
theorem ext3BinaryBasisVector_linearIndependent [Algebra (ZMod 2) Ext3] :
    LinearIndependent (ZMod 2) ext3BinaryBasisVector := by
  have hset : {x | x ∈ ext3BinaryBasis.toList} = Set.range ext3BinaryBasisVector := by
    ext x
    simp only [ext3BinaryBasis, Array.toList_ofFn, List.mem_ofFn, Set.mem_ofPred_eq,
      Set.mem_range]
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [← hset, ext3BinaryBasis_span]
  · rw [Fintype.card_fin, binary_finrank_of_card nat_card_ext3]

/-- The cubic extension's certified deterministic trace-splitting context. -/
def ext3SmallPrimeTraceContext : SmallPrimeTraceContext Ext3 := by
  letI := ZMod.algebra Ext3 2
  exact binaryTraceContextOfSpan 192 nat_card_ext3 ext3BinaryBasis (Array.size_ofFn ..)
    ext3BinaryBasis_span

/-- Certified BF64 field-root backend using binary trace coordinates. -/
def fieldRootContext : CompPoly.GuruswamiSudan.FieldRootContext BF64 :=
  CompPoly.GuruswamiSudan.finiteFieldRootContext BF64
    smallPrimeTraceContext.toFiniteFieldContext
    (shoupLinearFactorProductSplitter smallPrimeTraceContext)
    (rootProduct_satisfies_shoupSplitterInput _ _ smallPrimeTraceContext)

/-- Certified cubic-extension field-root backend using binary trace coordinates. -/
def ext3FieldRootContext : CompPoly.GuruswamiSudan.FieldRootContext Ext3 :=
  CompPoly.GuruswamiSudan.finiteFieldRootContext Ext3
    ext3SmallPrimeTraceContext.toFiniteFieldContext
    (shoupLinearFactorProductSplitter ext3SmallPrimeTraceContext)
    (rootProduct_satisfies_shoupSplitterInput _ _ ext3SmallPrimeTraceContext)

end BF64
