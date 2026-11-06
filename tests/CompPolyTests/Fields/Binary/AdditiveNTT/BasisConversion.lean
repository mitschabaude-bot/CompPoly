/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.AdditiveNTT.BasisConversion
public meta import CompPoly.Fields.Binary.BF64.Trace

/-!
# Executable monomial-to-novel conversion tests

The normalized degree-two basis over polynomial-basis BF64 has
`X² = X + 6 * novel[2]`, where 6 denotes the bit pattern `110`.
-/

public meta section

namespace CompPolyTests.Fields.Binary.AdditiveNTT.BasisConversion

open CompPoly _root_.AdditiveNTT

#guard monomialToNovelArray BF64.binaryBasisVector 2 (by decide)
  (CPolynomial.X ^ 2) == #[0, 1, BF64.ofBitVec 6, 0]

#guard monomialToNovelArray BF64.binaryBasisVector 0 (by decide)
  (CPolynomial.C (BF64.ofBitVec 17)) == #[BF64.ofBitVec 17]

#guard monomialToNovelArray BF64.binaryBasisVector 2 (by decide)
  (0 : CPolynomial BF64) == #[0, 0, 0, 0]

private def p : CPolynomial BF64 :=
  CPolynomial.ofArray #[BF64.ofBitVec 5, BF64.ofBitVec 9, BF64.ofBitVec 13, BF64.ofBitVec 21]

#guard
  let coeffs := monomialToNovelArray BF64.binaryBasisVector 2 (by decide) p
  let normalized := normalizedSubspacePolynomials BF64.binaryBasisVector 2 (by decide)
  let reconstructed := (List.range 4).foldl (fun acc i ↦
    acc + CPolynomial.C (coeffs.getD i 0) * novelBasisPolynomial normalized 2 i) 0
  reconstructed == p

end CompPolyTests.Fields.Binary.AdditiveNTT.BasisConversion
