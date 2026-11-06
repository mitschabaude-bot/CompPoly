/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.Trace
public import CompPoly.Bivariate.GuruswamiSudan.Parameters
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan
public import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
public import CompPoly.Univariate.SparseMul
public import CompPoly.Bivariate.GuruswamiSudan.Unique
public import CompPoly.Univariate.VanishingLinearized

/-!
# Certified scalar GS decoders over BF64 and Ext3

Concrete decoders combine finite parameter selection, Lee–O'Sullivan module
interpolation, and deterministic binary-trace root finding. Their coverage
theorem is independent of the received word's interpolation witness.
-/

@[expose] public section

namespace BF64

open CompPoly CompPoly.GuruswamiSudan

/-- Polynomial multiplication used by the binary-field structured decoder. -/
def structuredMulContext (F : Type*) [Field F] [BEq F] [LawfulBEq F] :
    CPolynomial.MulContext F := CPolynomial.MulContext.skipZeros

/-- Certified node vanishing polynomials for the structured binary-field decoder. -/
def structuredVanishingContext (F : Type*) [Field F] [BEq F] [LawfulBEq F] :
    CPolynomial.VanishingPolynomialContext F :=
  CPolynomial.VanishingPolynomialContext.linearized (structuredMulContext F)

/-- Lee–O'Sullivan interpolation with subproduct trees and shifted row reduction. -/
def structuredInterpolationContext (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] : GSInterpContext F :=
  LeeOSullivan.leeOSullivanInterpContext
    (structuredVanishingContext F)
    (CPolynomial.BatchEvalContext.subproduct F (structuredMulContext F)
      CPolynomial.ModContext.remainderOnly)
    (PolynomialMatrix.muldersStorjohannFastReducerContext F)

/-- Concrete structured scalar decoder context over the base field. -/
def gsFilteredCoreContext : GSFilteredCoreContext BF64 :=
  filteredCoreContextOfInterpRootContexts (structuredInterpolationContext BF64)
    (rothRuckensteinRootContext BF64 fieldRootContext)

/-- Concrete structured scalar decoder context over the cubic extension. -/
def ext3GSFilteredCoreContext : GSFilteredCoreContext Ext3 :=
  filteredCoreContextOfInterpRootContexts (structuredInterpolationContext Ext3)
    (rothRuckensteinRootContext Ext3 ext3FieldRootContext)

/-- Executable base-field scalar list decoding with certified finite parameter selection. -/
def decodeScalar (k e : Nat) (w : GSReceivedWord BF64) : Array (CPolynomial BF64) :=
  decodeWithUnique gsFilteredCoreContext k e w

/-- Executable extension-field scalar list decoding with certified parameter selection. -/
def decodeExt3Scalar (k e : Nat) (w : GSReceivedWord Ext3) : Array (CPolynomial Ext3) :=
  decodeWithUnique ext3GSFilteredCoreContext k e w

/-- Exact base-field scalar coverage when finite parameter selection succeeds. -/
theorem mem_decodeScalar_iff {k e : Nat} (w : GSReceivedWord BF64)
    {params : GSExecParams}
    (hselect : finiteGSParamSelector.choose k w.length e = some params)
    (hdistinct : DistinctXCoordinates w.points) (p : CPolynomial BF64) :
    p ∈ (decodeScalar k e w).toList ↔
      degreeLt p k ∧ candidateMismatchCount w.points p ≤ e :=
  mem_decodeWithUnique_iff gsFilteredCoreContext w hselect hdistinct p

/-- Exact extension-field scalar coverage when finite parameter selection succeeds. -/
theorem mem_decodeExt3Scalar_iff {k e : Nat} (w : GSReceivedWord Ext3)
    {params : GSExecParams}
    (hselect : finiteGSParamSelector.choose k w.length e = some params)
    (hdistinct : DistinctXCoordinates w.points) (p : CPolynomial Ext3) :
    p ∈ (decodeExt3Scalar k e w).toList ↔
      degreeLt p k ∧ candidateMismatchCount w.points p ≤ e :=
  mem_decodeWithUnique_iff ext3GSFilteredCoreContext w hselect hdistinct p

end BF64
