/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.BF64.GuruswamiSudan

/-!
# Executable scalar GS decoding

Small base-field and extension-field received words exercise the certified
parameter selector, structured interpolator, and root reconstruction together.
-/

public meta section

namespace CompPolyTests.Fields.Binary.BF64.GuruswamiSudan

open CompPoly CompPoly.GuruswamiSudan

private def p : CPolynomial BF64 := CPolynomial.ofArray #[BF64.ofBitVec 7, BF64.ofBitVec 3]

private def word : GSReceivedWord BF64 :=
  ⟨Array.ofFn fun i : Fin 4 ↦
    let x := BF64.ofBitVec (BitVec.ofNat 64 i.val)
    (x, CPolynomial.eval x p)⟩

#guard (BF64.decodeScalar 2 0 word).contains p

#guard (BF64.decodeScalar 2 1 ⟨word.points.set! 0 (0, BF64.ofBitVec 99)⟩).contains p
#guard (BF64.decodeScalar 2 4 word).isEmpty

private def ep : CPolynomial BF64.Ext3 :=
  CPolynomial.ofArray #[BF64.ext3Gen, BF64.ext3Gen ^ 2]

private def eword : GSReceivedWord BF64.Ext3 :=
  ⟨Array.ofFn fun i : Fin 4 ↦
    let x := CompPoly.Extension.Ext.ofBase (BF64.ofBitVec (BitVec.ofNat 64 i.val))
    (x, CPolynomial.eval x ep)⟩

#guard (BF64.decodeExt3Scalar 2 0 eword).contains ep

private def polynomialCases : Array (CPolynomial BF64) :=
  #[0, 1, p, CPolynomial.ofArray #[1, 0, 0, 0, BF64.ofBitVec 99],
    CPolynomial.ofArray #[0, 1, BF64.ofBitVec 7, BF64.ofBitVec 13]]

#guard polynomialCases.all fun p ↦ polynomialCases.all fun q ↦
  (BF64.structuredMulContext BF64).mul p q == p * q

#guard (normalizeVector? (#[] : Array BF64)).isNone
#guard (normalizeVector? (#[0, 0, 0] : Array BF64)).isNone
#guard (normalizeVector? (#[0, 0, 1, 0, 1] : Array BF64)) == some #[0, 0, 1, 0, 1]
#guard polynomialCases.all fun p ↦
  let v : Array BF64 := #[0, 0] ++ p.val.coeffs
  normalizeVector? v == match firstNonzeroIndex? v with
    | none => none
    | some i => some (v.map fun c ↦ c / v.getD i 0)

private def denseP : CPolynomial BF64 :=
  CPolynomial.ofArray ((Array.range 8).map fun i ↦
    BF64.ofBitVec (BitVec.ofNat 64 (0x9e3779b97f4a7c15 + 17 * i)))

private def denseWord : GSReceivedWord BF64 :=
  ⟨(Array.range 16).map fun i ↦
    let x := BF64.ofBitVec (BitVec.ofNat 64 i)
    (x, CPolynomial.eval x denseP)⟩

#guard let result := BF64.decodeScalar 8 1 denseWord
  result.size == 1 && result.contains denseP

private def denseEP : CPolynomial BF64.Ext3 :=
  CPolynomial.ofArray ((Array.range 4).map fun i ↦
    CompPoly.Extension.Ext.ofFn fun j ↦
      BF64.ofBitVec (BitVec.ofNat 64 (1234567 + 17 * i + 31 * j.val)))

private def denseEWord : GSReceivedWord BF64.Ext3 :=
  ⟨(Array.range 8).map fun i ↦
    let x := CompPoly.Extension.Ext.ofBase (BF64.ofBitVec (BitVec.ofNat 64 i))
    (x, CPolynomial.eval x denseEP)⟩

#guard let result := BF64.decodeExt3Scalar 4 1 denseEWord
  result.size == 1 && result.contains denseEP

end CompPolyTests.Fields.Binary.BF64.GuruswamiSudan
