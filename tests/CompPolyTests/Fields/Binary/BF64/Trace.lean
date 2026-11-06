/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.BF64.Trace

/-!
# Executable binary-field trace splitting

Root extraction exercises non-prime-field bits, extension limbs, constants,
and zero. These checks execute the certified contexts.
-/

public meta section

namespace CompPolyTests.Fields.Binary.BF64.Trace

open CompPoly

private def a : BF64 := BF64.ofBitVec 0x123456789abcdef0
private def b : BF64 := BF64.ofBitVec 0x323456789abcdef0
private def p : CPolynomial BF64 :=
  CPolynomial.linearFactor a
private def roots : Array BF64 := BF64.fieldRootContext.rootsInField p

#guard let rs := roots; rs.size == 1 && rs.contains a
#guard (BF64.fieldRootContext.rootsInField 0).isEmpty
#guard (BF64.fieldRootContext.rootsInField 1).isEmpty
#guard BF64.smallPrimeTraceContext.basis.size == 64
#guard BF64.smallPrimeTraceContext.traceValue (a * b) == 0 ||
  BF64.smallPrimeTraceContext.traceValue (a * b) == 1

private def ea : BF64.Ext3 :=
  CompPoly.Extension.Ext.ofBase a + BF64.ext3Gen
private def ep : CPolynomial BF64.Ext3 :=
  CPolynomial.linearFactor ea
private def eroots : Array BF64.Ext3 := BF64.ext3FieldRootContext.rootsInField ep

#guard let rs := eroots; rs.size == 1 && rs.contains ea
#guard BF64.ext3SmallPrimeTraceContext.basis.size == 192

end CompPolyTests.Fields.Binary.BF64.Trace
