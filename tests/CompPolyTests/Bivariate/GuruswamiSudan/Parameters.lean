/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Bivariate.GuruswamiSudan.Parameters.Correctness
public meta import CompPoly.Bivariate.GuruswamiSudan.Parameters.Basic

/-!
# Certified finite parameter selection tests

The production dimensions and integer mismatch radii select multiplicities
one, one, and two. Rejected inputs exercise the explicit failure boundary.
-/

public section

set_option maxRecDepth 65536

namespace CompPolyTests.GuruswamiSudan.Parameters

open CompPoly.GuruswamiSudan

/-- The initial production code has a multiplicity-one parameter certificate. -/
theorem initial_selection : finiteGSParamSelector.choose 8192 16384 937 =
    some { interp := ⟨8192, 1, 15446⟩, radius := 937 } := by decide

/-- The middle production code has a multiplicity-one parameter certificate. -/
theorem middle_selection : finiteGSParamSelector.choose 512 8192 5464 =
    some { interp := ⟨512, 1, 2727⟩, radius := 5464 } := by decide

/-- The final production code has a multiplicity-two parameter certificate. -/
theorem final_selection : finiteGSParamSelector.choose 32 4096 3620 =
    some { interp := ⟨32, 2, 951⟩, radius := 3620 } := by decide

#guard (finiteGSParamSelector.choose 1 8 2).isNone
#guard (finiteGSParamSelector.choose 4 8 8).isNone
#guard (finiteGSParamSelector.choose 4 0 0).isNone
#guard interpolationMonomialCount ⟨8192, 1, 15446⟩ == 22703
#guard interpolationMonomialCount ⟨512, 1, 2727⟩ == 8703
#guard interpolationMonomialCount ⟨32, 2, 951⟩ == 15097

end CompPolyTests.GuruswamiSudan.Parameters
