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

end CompPolyTests.Fields.Binary.BF64.GuruswamiSudan
