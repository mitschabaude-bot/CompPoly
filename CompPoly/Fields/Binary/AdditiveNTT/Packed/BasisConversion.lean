/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Encoder
public import CompPoly.Fields.Binary.AdditiveNTT.BasisConversion

/-!
# Monomial polynomials to packed novel coefficients

Triangular basis conversion is separate from the inverse transform. Its
reconstruction theorem certifies the polynomial represented by each packed lane.
-/

@[expose] public section

namespace AdditiveNTT.Packed

open BF64 CompPoly

/-- Convert monomial polynomials into row-major novel coefficients for encoding. -/
def monomialCoefficients (ell : Nat) (hell : ell ≤ 64) (lanes : Nat)
    (polys : Fin lanes → CPolynomial Word) : BF64.Packed.Buffer (2 ^ ell * lanes) :=
  tabulate _ fun j =>
    let ix := finProdFinEquiv.symm j
    (monomialToNovelArray flatBasis ell hell (polys ix.2)).getD ix.1.val 0

/-- Each lane contains exactly the executable triangular basis conversion. -/
theorem laneView_monomialCoefficients (ell : Nat) (hell : ell ≤ 64) (lanes : Nat)
    (polys : Fin lanes → CPolynomial Word) (lane : Fin lanes) :
    laneView (monomialCoefficients ell hell lanes polys) lane =
      fun j => (monomialToNovelArray flatBasis ell hell (polys lane)).getD j.val 0 := by
  funext row
  simp only [laneView, monomialCoefficients, read_tabulate, Equiv.symm_apply_apply]

/-- Packed coefficients reconstruct each source polynomial in the mathematical novel basis. -/
theorem monomialCoefficients_reconstruct [Fintype Word] (ell : Nat) (hell : ell ≤ 64) (lanes : Nat)
    (polys : Fin lanes → CPolynomial Word) (lane : Fin lanes)
    (hp : (polys lane).toPoly.degree < (2 ^ ell : Nat)) :
    ∑ j : Fin (2 ^ ell),
      Polynomial.C (laneView (monomialCoefficients ell hell lanes polys) lane j) *
        Xⱼ (ZMod 2) flatBasis ell hell j = (polys lane).toPoly := by
  classical
  rw [laneView_monomialCoefficients]
  exact monomialToNovelArray_reconstruct (ZMod 2) flatBasis ell hell (polys lane) hp

end AdditiveNTT.Packed
