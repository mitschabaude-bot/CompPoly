/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Bivariate.GuruswamiSudan.Executable
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic

/-!
# Finite Guruswami–Sudan parameter selection

The selector searches positive multiplicities bounded by the word length. Its
integer tests certify dimension slack and the strict agreement inequality.
Monomial counts use row lengths rather than a square of exponent pairs.
-/

@[expose] public section

namespace CompPoly.GuruswamiSudan

/-- A compact weighted-degree basis, ordered by `Y` degree and then `X` degree. -/
def compactInterpolationMonomials (params : GSInterpParams) : Array CBivariate.Monomial :=
  ((List.range (interpolationYCap params + 1)).flatMap fun y ↦
    (List.range (params.weightedDegreeBound - yWeight params * y + 1)).map fun x ↦
      ({ xDegree := x, yDegree := y } : CBivariate.Monomial)).toArray

/-- Number of monomials in the compact interpolation basis. -/
def interpolationMonomialCount (params : GSInterpParams) : Nat :=
  ((List.range (interpolationYCap params + 1)).map fun y ↦
    params.weightedDegreeBound - yWeight params * y + 1).sum

/-- Number of Hasse constraints contributed by one interpolation point. -/
def interpolationConstraintCount (multiplicity : Nat) : Nat :=
  ((List.range multiplicity).map fun a ↦ multiplicity - a).sum

/-- Parameters with the largest weighted-degree bound strictly below `s * (n-e)`. -/
def agreementInterpParams (k n e s : Nat) : GSInterpParams where
  messageDegree := k
  multiplicity := s
  weightedDegreeBound := s * (n - e) - 1

/-- Finite integer certificate checked by the parameter selector. -/
def parameterDimensionTest (k n e s : Nat) : Bool :=
  decide (n * interpolationConstraintCount s <
    interpolationMonomialCount (agreementInterpParams k n e s))

/-- Select a positive multiplicity using only bounded natural-number arithmetic.

The mismatch radius is `e`; success requires a positive agreement cutoff and
positive `Y` weight. Failure is explicit when no certified multiplicity in
`[1,n]` is found.
-/
def finiteGSParamSelector : GSParamSelector where
  choose k n e :=
    if 1 < k ∧ e < n then
      ((List.range n).find? fun i ↦ parameterDimensionTest k n e (i + 1)).map fun i ↦
        { interp := agreementInterpParams k n e (i + 1), radius := e }
    else none

end CompPoly.GuruswamiSudan
