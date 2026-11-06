/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Bivariate.GuruswamiSudan.Parameters.Correctness

/-!
# Production GS parameter certificates

Kernel-checked selections for message dimensions 8192, 512, and 32, with
word lengths 16384, 8192, and 4096 and mismatch radii 937, 5464, and 3620.
-/

public section

namespace CompPoly.GuruswamiSudan

set_option maxRecDepth 65536 in
/-- Multiplicity-one parameters for the initial production code. -/
theorem finiteGSParamSelector_initial : finiteGSParamSelector.choose 8192 16384 937 =
    some { interp := ⟨8192, 1, 15446⟩, radius := 937 } := by decide

set_option maxRecDepth 65536 in
/-- Multiplicity-one parameters for the middle production code. -/
theorem finiteGSParamSelector_middle : finiteGSParamSelector.choose 512 8192 5464 =
    some { interp := ⟨512, 1, 2727⟩, radius := 5464 } := by decide

set_option maxRecDepth 65536 in
/-- Multiplicity-two parameters for the final production code. -/
theorem finiteGSParamSelector_final : finiteGSParamSelector.choose 32 4096 3620 =
    some { interp := ⟨32, 2, 951⟩, radius := 3620 } := by decide

/-- Exact scalar coverage at the initial production dimensions and mismatch radius. -/
theorem mem_decode_initial_iff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ctx : GSFilteredCoreContext F) (w : GSReceivedWord F) (hlen : w.length = 16384)
    (hdistinct : DistinctXCoordinates w.points) (p : CPolynomial F) :
    p ∈ (decode ctx finiteGSParamSelector 8192 937 w).toList ↔
      degreeLt p 8192 ∧ candidateMismatchCount w.points p ≤ 937 :=
  mem_decode_finiteGSParamSelector_iff ctx w
    (by rw [hlen]; exact finiteGSParamSelector_initial) hdistinct p

/-- Exact scalar coverage at the middle production dimensions and mismatch radius. -/
theorem mem_decode_middle_iff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ctx : GSFilteredCoreContext F) (w : GSReceivedWord F) (hlen : w.length = 8192)
    (hdistinct : DistinctXCoordinates w.points) (p : CPolynomial F) :
    p ∈ (decode ctx finiteGSParamSelector 512 5464 w).toList ↔
      degreeLt p 512 ∧ candidateMismatchCount w.points p ≤ 5464 :=
  mem_decode_finiteGSParamSelector_iff ctx w
    (by rw [hlen]; exact finiteGSParamSelector_middle) hdistinct p

/-- Exact scalar coverage at the final production dimensions and mismatch radius. -/
theorem mem_decode_final_iff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ctx : GSFilteredCoreContext F) (w : GSReceivedWord F) (hlen : w.length = 4096)
    (hdistinct : DistinctXCoordinates w.points) (p : CPolynomial F) :
    p ∈ (decode ctx finiteGSParamSelector 32 3620 w).toList ↔
      degreeLt p 32 ∧ candidateMismatchCount w.points p ≤ 3620 :=
  mem_decode_finiteGSParamSelector_iff ctx w
    (by rw [hlen]; exact finiteGSParamSelector_final) hdistinct p

end CompPoly.GuruswamiSudan
