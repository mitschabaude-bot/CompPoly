/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Basic
public import CompPoly.Univariate.SparseMul
public import CompPoly.Univariate.ToPoly.RingHom

/-! # Sparse vanishing powers in the Lee–O'Sullivan lattice basis -/

@[expose] public section

namespace CompPoly.GuruswamiSudan

/-- Construct lattice rows with sparse vanishing-polynomial arithmetic. -/
def leeOSullivanBasisRowsSparse {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (R G : CPolynomial F) (params : GSInterpParams) : PolynomialMatrix F :=
  let width := leeOSullivanWidth params
  (List.range width).map (fun i ↦
    let t := leeOSullivanT params i
    let exponent := params.multiplicity - t
    let power := if exponent = 2 then CPolynomial.MulContext.skipZeros.mul G G else G ^ exponent
    CBivariate.toCoeffRow width
      ((CBivariate.Y : CBivariate F) ^ (i - t) * (CBivariate.linearYDivisor R) ^ t *
        CBivariate.ofYConstant power)) |>.toArray

/-- Sparse vanishing powers preserve every coefficient of the lattice basis. -/
@[csimp] theorem leeOSullivanBasisRows_eq_sparse :
    @leeOSullivanBasisRowsWithRG = @leeOSullivanBasisRowsSparse := by
  funext F _ _ _ _ R G params
  have hpower (n : Nat) :
      CBivariate.ofYConstant
        (if n = 2 then CPolynomial.MulContext.skipZeros.mul G G else G ^ n) =
      (CBivariate.ofYConstant G : CBivariate F) ^ n := by
    have h : (if n = 2 then CPolynomial.MulContext.skipZeros.mul G G else G ^ n) =
        G ^ n := by
      split_ifs with hn
      · subst n
        rw [CPolynomial.MulContext.mul_eq_mul, pow_two]
      · rfl
    rw [h]
    exact map_pow (CPolynomial.CHom (R := CPolynomial F)) G n
  simp only [leeOSullivanBasisRowsWithRG, leeOSullivanBasisRowsSparse,
    leeOSullivanBasisPolynomial, hpower]

end CompPoly.GuruswamiSudan
