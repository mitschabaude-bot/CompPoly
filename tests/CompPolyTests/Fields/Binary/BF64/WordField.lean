/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.BF64.GuruswamiSudan
public meta import CompPoly.Univariate.BinarySquare

/-! # Executable word fields and characteristic-two polynomial squares -/

public meta section

open BF64 CompPoly

private def a : Word := ⟨0x0123456789abcdef⟩
private def b : Word := ⟨0xfedcba9876543210⟩
private def x : WordExt3 := ⟨a, b, a + b⟩
private def y : WordExt3 := ⟨b, a, a * b⟩

#guard (a * b).toField == a.toField * b.toField
#guard (a⁻¹).toField == (a.toField)⁻¹
#guard a * a⁻¹ == 1
#guard (0 : Word)⁻¹ == 0
#guard (x * y).toField == x.toField * y.toField
#guard (x + y).toField == x.toField + y.toField
#guard (-x) == x
#guard x - y == x + y
#guard x * x⁻¹ == 1
#guard (0 : WordExt3)⁻¹ == 0

private def ps : Array (CPolynomial Word) :=
  #[0, 1, CPolynomial.ofArray #[a, b, 0, a + b],
    CPolynomial.ofArray ((Array.range 32).map fun i ↦ ⟨UInt64.ofNat (i * 37 + 9)⟩)]

#guard ps.all fun p ↦ CPolynomial.binarySquare p == p * p
#guard ps.all fun p ↦
  CPolynomial.mapCoeffs Word.ringEquiv.symm (CPolynomial.mapCoeffs Word.ringEquiv p) == p
