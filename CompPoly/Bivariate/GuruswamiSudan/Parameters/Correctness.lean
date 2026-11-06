/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Bivariate.GuruswamiSudan.Parameters.Basic
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness

/-!
# Certified parameter selection and interpolation existence

Successful finite parameter selection guarantees a nonzero interpolation
witness for every received word of the selected length. The existence proof
uses the compact basis and the dense kernel theorem only in `Prop`; executable
decoders can use any certified structured interpolation backend.
-/

public section

namespace CompPoly.GuruswamiSudan

/-- The compact basis has the count used by parameter selection. -/
theorem compactInterpolationMonomials_size (params : GSInterpParams) :
    (compactInterpolationMonomials params).size = interpolationMonomialCount params := by
  simp only [compactInterpolationMonomials, interpolationMonomialCount, List.size_toArray,
    List.length_flatMap, List.length_map, List.length_range]

/-- Every compact-basis monomial satisfies the interpolation weighted-degree bound. -/
theorem compactInterpolationMonomials_sound (params : GSInterpParams)
    {m : CBivariate.Monomial} (hm : m ∈ (compactInterpolationMonomials params).toList) :
    1 * m.xDegree + yWeight params * m.yDegree ≤ params.weightedDegreeBound := by
  simp only [compactInterpolationMonomials, List.toList_toArray, List.mem_flatMap,
    List.mem_map, List.mem_range] at hm
  obtain ⟨y, hy, x, hx, rfl⟩ := hm
  have hy' : y ≤ params.weightedDegreeBound / yWeight params := by
    simpa only [interpolationYCap] using Nat.le_of_lt_succ hy
  have hmul : yWeight params * y ≤ params.weightedDegreeBound :=
    (Nat.mul_le_mul_left (yWeight params) hy').trans (Nat.mul_div_le _ _)
  dsimp
  omega

/-- The compact interpolation basis contains no repeated exponent pairs. -/
theorem compactInterpolationMonomials_nodup (params : GSInterpParams) :
    (compactInterpolationMonomials params).toList.Nodup := by
  simp only [compactInterpolationMonomials, List.toList_toArray]
  rw [List.nodup_flatMap]
  constructor
  · intro y _
    exact List.nodup_range.map (by
      intro x₁ x₂ h
      cases h
      rfl)
  · exact List.nodup_range.pairwise_of_forall_ne (by
      intro y _ y' _ hyne
      simp only [Function.onFun, List.disjoint_left]
      intro m hm hm'
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm
      obtain ⟨x', _, heq⟩ := List.mem_map.mp hm'
      exact hyne (by cases heq; rfl))

private theorem foldl_size_add {α β : Type*} (step : Array β → α → Array β)
    (weight : α → Nat) (hstep : ∀ out x, (step out x).size = out.size + weight x)
    (xs : List α) (out : Array β) :
    (xs.foldl step out).size = out.size + (xs.map weight).sum := by
  induction xs generalizing out with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, hstep, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- Packed Hasse constraints have the count used by parameter selection. -/
theorem interpolationConstraints_size {F : Type*} (points : Array (F × F)) (s : Nat) :
    (interpolationConstraints points s).size = points.size * interpolationConstraintCount s := by
  unfold interpolationConstraints
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, tsub_zero,
    add_tsub_cancel_right, Nat.div_one, List.forIn_pure_yield_eq_foldl,
    List.foldl_push_eq_append, bind_pure_comp, map_pure,
    Array.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
  rw [← Array.foldl_toList]
  have hinner (point : F × F) (a : Nat) (out : Array (InterpolationConstraint F)) :
      (out ++ (List.map (InterpolationConstraint.mk point.1 point.2 a)
        (List.range' 0 (s - a))).toArray).size = out.size + (s - a) := by
    simp only [Array.size_append, List.size_toArray, List.length_map, List.length_range']
  have hpoint (out : Array (InterpolationConstraint F)) (point : F × F) :
      ((List.range' 0 s).foldl (fun out a ↦ out ++
        (List.map (InterpolationConstraint.mk point.1 point.2 a)
          (List.range' 0 (s - a))).toArray) out).size =
        out.size + interpolationConstraintCount s := by
    rw [foldl_size_add _ (fun a ↦ s - a) (fun out a ↦ hinner point a out)]
    simp only [interpolationConstraintCount, List.range_eq_range']
  rw [foldl_size_add _ (fun _ ↦ interpolationConstraintCount s) hpoint]
  simp only [Array.size_empty, Nat.zero_add, List.map_const', List.sum_replicate,
    Array.length_toList, smul_eq_mul]

/-- Hasse constraints at multiplicity `s` form a triangular set of derivative orders. -/
theorem interpolationConstraintCount_succ (s : Nat) :
    interpolationConstraintCount (s + 1) = interpolationConstraintCount s + (s + 1) := by
  unfold interpolationConstraintCount
  rw [List.range_succ, List.map_append, List.sum_append]
  have heq : (List.range s).map (fun a ↦ s + 1 - a) =
      (List.range s).map (fun a ↦ (s - a) + 1) := by
    apply List.map_congr_left
    intro a ha
    have := List.mem_range.mp ha
    omega
  rw [heq, List.sum_map_add]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.add_sub_cancel_left, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul, Nat.mul_one]
  change ((List.range s).map (fun a ↦ s - a)).sum + s + 1 =
    ((List.range s).map (fun a ↦ s - a)).sum + (s + 1)
  omega

/-- The number of Hasse constraints per point is `s * (s + 1) / 2`. -/
theorem interpolationConstraintCount_eq (s : Nat) :
    interpolationConstraintCount s = s * (s + 1) / 2 := by
  have htwice : 2 * interpolationConstraintCount s = s * (s + 1) := by
    induction s with
    | zero => rfl
    | succ s ih => rw [interpolationConstraintCount_succ]; nlinarith
  omega

/-- Dimension slack alone gives a semantic interpolation witness on the compact basis. -/
theorem interpolationWitness_exists_of_count_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams)
    (hcount : points.size * interpolationConstraintCount params.multiplicity <
      interpolationMonomialCount params) :
    ∃ Q, ValidInterpolationWitness points params Q := by
  obtain ⟨Q, hQ⟩ := denseInterpolateWithBasis_exists_of_dimension_slack
    (compactInterpolationMonomials params) points params (by
      simpa only [HasInterpolationDimensionSlackOnBasis, interpolationConstraints_size,
        compactInterpolationMonomials_size] using hcount)
  exact ⟨Q, denseInterpolateWithBasisAndKernel_sound_of_bounded_basis
    (compactInterpolationMonomials_nodup params)
    (fun _ hm ↦ compactInterpolationMonomials_sound params hm) hQ⟩

/-- Every successful selection certifies the requested degree, radius, dimension,
and strict agreement inequality. -/
theorem finiteGSParamSelector_spec {k n e : Nat} {params : GSExecParams}
    (h : finiteGSParamSelector.choose k n e = some params) :
    1 < k ∧ e < n ∧ params.interp.messageDegree = k ∧ params.radius = e ∧
      0 < params.interp.multiplicity ∧ params.interp.multiplicity ≤ n ∧
      params.interp.weightedDegreeBound < params.interp.multiplicity * (n - e) ∧
      n * interpolationConstraintCount params.interp.multiplicity <
        interpolationMonomialCount params.interp := by
  simp only [finiteGSParamSelector] at h
  split at h
  next hvalid =>
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
    have hmem := List.mem_of_find?_eq_some hi
    have htest := List.find?_some hi
    simp only [List.mem_range] at hmem
    simp only [parameterDimensionTest, decide_eq_true_eq] at htest
    refine ⟨hvalid.1, hvalid.2, rfl, rfl, Nat.succ_pos _, by change i + 1 ≤ n; omega, ?_, htest⟩
    change (i + 1) * (n - e) - 1 < (i + 1) * (n - e)
    exact Nat.sub_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt hvalid.2))
      (by decide)
  next => simp only [reduceCtorEq] at h

/-- A successful selection discharges interpolation existence for every word of length `n`. -/
theorem finiteGSParamSelector_interpolation_exists {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    {k n e : Nat} {params : GSExecParams}
    (h : finiteGSParamSelector.choose k n e = some params)
    (points : Array (F × F)) (hlen : points.size = n) :
    ∃ Q, ValidInterpolationWitness points params.interp Q := by
  apply interpolationWitness_exists_of_count_lt
  rw [hlen]
  exact (finiteGSParamSelector_spec h).2.2.2.2.2.2.2

/-- Matching and mismatching packed points partition the received word. -/
theorem matchingPointCount_add_candidateMismatchCount {F : Type*} [Semiring F] [BEq F]
    (points : Array (F × F)) (p : CPolynomial F) :
    matchingPointCount points p + candidateMismatchCount points p = points.size := by
  unfold matchingPointCount candidateMismatchCount
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have h (xs : List (F × F)) (a b : Nat) :
      xs.foldl (fun count point ↦
        if CPolynomial.eval point.1 p == point.2 then count + 1 else count) a +
      xs.foldl (fun count point ↦
        if CPolynomial.eval point.1 p == point.2 then count else count + 1) b =
      a + b + xs.length := by
    induction xs generalizing a b with
    | nil => simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      split <;> rw [ih] <;> omega
  simpa only [Nat.zero_add, Array.length_toList] using h points.toList 0 0

/-- The mismatch filter is exactly the natural-number agreement cutoff. -/
theorem passesCandidateDistance_iff_agreement {F : Type*} [Semiring F] [BEq F]
    (points : Array (F × F)) (p : CPolynomial F) {e : Nat} (he : e ≤ points.size) :
    passesCandidateDistance points e p = true ↔
      points.size - e ≤ matchingPointCount points p := by
  rw [passesCandidateDistance_iff]
  have := matchingPointCount_add_candidateMismatchCount points p
  omega

/-- Successful parameter selection gives exact decoder coverage without a per-word
interpolation-existence hypothesis. -/
theorem mem_decode_finiteGSParamSelector_iff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ctx : GSFilteredCoreContext F) {k e : Nat} (w : GSReceivedWord F)
    {params : GSExecParams}
    (hselect : finiteGSParamSelector.choose k w.length e = some params)
    (hdistinct : DistinctXCoordinates w.points) (p : CPolynomial F) :
    p ∈ (decode ctx finiteGSParamSelector k e w).toList ↔
      degreeLt p k ∧ candidateMismatchCount w.points p ≤ e := by
  have hs := finiteGSParamSelector_spec hselect
  simp only [decode, hselect, decodeWithParams]
  constructor
  · intro hp
    obtain ⟨Q, _, hdeg, _, hdist⟩ := ctx.sound hp
    exact ⟨hs.2.2.1 ▸ hdeg, hs.2.2.2.1 ▸ hdist⟩
  · rintro ⟨hdeg, hdist⟩
    apply ctx.complete
    · exact finiteGSParamSelector_interpolation_exists hselect w.points rfl
    · exact hdistinct
    · rw [hs.2.2.1]
      exact hdeg
    · apply lt_of_lt_of_le hs.2.2.2.2.2.2.1
      apply Nat.mul_le_mul_left
      have hcounts := matchingPointCount_add_candidateMismatchCount w.points p
      change w.points.size - e ≤ matchingPointCount w.points p
      omega
    · rw [passesCandidateDistance_iff, hs.2.2.2.1]
      exact hdist

end CompPoly.GuruswamiSudan
