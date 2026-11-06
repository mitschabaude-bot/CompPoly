/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
public import CompPoly.Bivariate.GuruswamiSudan.Unique
public import CompPoly.Univariate.ToPoly.RingHom

/-! # Transporting certified decoder families across field isomorphisms -/

@[expose] public section

namespace CompPoly.CPolynomial

variable {F K : Type*} [Field F] [Field K]
variable [BEq F] [LawfulBEq F] [BEq K] [LawfulBEq K]

/-- Linear-time coefficient transport, including canonical trimming. -/
def mapCoeffs (e : F ≃+* K) (p : CPolynomial F) : CPolynomial K :=
  ofArray (p.val.map e)

omit [BEq F] [LawfulBEq F] in
@[simp] theorem coeff_mapCoeffs (e : F ≃+* K) (p : CPolynomial F) (i : Nat) :
    (mapCoeffs e p).coeff i = e (p.coeff i) := by
  rw [mapCoeffs, coeff_ofArray]
  change (p.val.map e).getD i 0 = e (p.val.getD i 0)
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases p.val[i]? <;> simp only [Option.map_none, Option.getD_none, map_zero,
    Option.map_some, Option.getD_some]

/-- Coefficient transport agrees with Mathlib's polynomial map. -/
theorem toPoly_mapCoeffs (e : F ≃+* K) (p : CPolynomial F) :
    (mapCoeffs e p).toPoly = p.toPoly.map e.toRingHom := by
  ext i
  simp only [← coeff_toPoly, coeff_mapCoeffs, Polynomial.coeff_map]
  rfl

@[simp] theorem mapCoeffs_symm (e : F ≃+* K) (p : CPolynomial F) :
    mapCoeffs e.symm (mapCoeffs e p) = p := by
  apply toPoly_injective
  ext i
  simp only [← coeff_toPoly, coeff_mapCoeffs, RingEquiv.symm_apply_apply]

@[simp] theorem eval_mapCoeffs (e : F ≃+* K) (p : CPolynomial F) (x : F) :
    eval (e x) (mapCoeffs e p) = e (eval x p) := by
  rw [eval_toPoly, toPoly_mapCoeffs, eval_toPoly]
  exact Polynomial.eval_map_apply e.toRingHom x

@[simp] theorem degree_mapCoeffs (e : F ≃+* K) (p : CPolynomial F) :
    (mapCoeffs e p).degree = p.degree := by
  rw [degree_toPoly, degree_toPoly, toPoly_mapCoeffs,
    Polynomial.degree_map_eq_of_injective e.injective]

end CompPoly.CPolynomial

namespace CompPoly.GuruswamiSudan

variable {F K : Type*} [Field F] [Field K]
variable [BEq F] [LawfulBEq F] [BEq K] [LawfulBEq K]

/-- Map the abscissas and values of a packed received word. -/
def mapReceivedWord (e : F ≃+* K) (w : GSReceivedWord F) : GSReceivedWord K :=
  ⟨w.points.map fun (x, y) ↦ (e x, e y)⟩

omit [BEq F] [LawfulBEq F] [BEq K] [LawfulBEq K] in
@[simp] theorem length_mapReceivedWord (e : F ≃+* K) (w : GSReceivedWord F) :
    (mapReceivedWord e w).length = w.length := by
  simp only [mapReceivedWord, GSReceivedWord.length, Array.size_map]

omit [BEq F] [LawfulBEq F] [BEq K] [LawfulBEq K] in
/-- Distinct abscissas are preserved by field transport. -/
theorem distinct_mapReceivedWord (e : F ≃+* K) (w : GSReceivedWord F)
    (hd : DistinctXCoordinates w.points) :
    DistinctXCoordinates (mapReceivedWord e w).points := by
  simpa only [DistinctXCoordinates, mapReceivedWord, Array.toList_map, List.map_map,
    Function.comp_def] using hd.map e.injective

@[simp] theorem mismatch_mapReceivedWord (e : F ≃+* K) (w : GSReceivedWord F)
    (p : CPolynomial F) :
    candidateMismatchCount (mapReceivedWord e w).points (CPolynomial.mapCoeffs e p) =
      candidateMismatchCount w.points p := by
  unfold candidateMismatchCount mapReceivedWord
  rw [Array.foldl_map]
  congr 1
  funext count point
  simp only [CPolynomial.eval_mapCoeffs]
  have h : (e (CPolynomial.eval point.1 p) == e point.2) =
      (CPolynomial.eval point.1 p == point.2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, e.injective.eq_iff]
  rw [h]

variable [DecidableEq F] [DecidableEq K]

/-- Run a certified decoder on an isomorphic executable field and map its answers back. -/
def decodeMapped (e : K ≃+* F) (ctx : GSFilteredCoreContext K)
    (k radius : Nat) (w : GSReceivedWord F) : Array (CPolynomial F) :=
  (decodeWithUnique ctx k radius (mapReceivedWord e.symm w)).map
    (CPolynomial.mapCoeffs e)

omit [DecidableEq F] in
/-- Exact coverage is invariant under field isomorphism. -/
theorem mem_decodeMapped_iff (e : K ≃+* F) (ctx : GSFilteredCoreContext K)
    {k radius : Nat} (w : GSReceivedWord F) {params : GSExecParams}
    (hselect : finiteGSParamSelector.choose k w.length radius = some params)
    (hd : DistinctXCoordinates w.points) (p : CPolynomial F) :
    p ∈ (decodeMapped e ctx k radius w).toList ↔
      degreeLt p k ∧ candidateMismatchCount w.points p ≤ radius := by
  have hc := mem_decodeWithUnique_iff ctx (mapReceivedWord e.symm w)
    (by simpa only [length_mapReceivedWord] using hselect)
    (distinct_mapReceivedWord e.symm w hd) (CPolynomial.mapCoeffs e.symm p)
  rw [degreeLt, CPolynomial.degree_mapCoeffs, mismatch_mapReceivedWord] at hc
  rw [decodeMapped, Array.toList_map, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' := (mem_decodeWithUnique_iff ctx (mapReceivedWord e.symm w)
      (by simpa only [length_mapReceivedWord] using hselect)
      (distinct_mapReceivedWord e.symm w hd) q).mp hq
    rw [degreeLt, CPolynomial.degree_mapCoeffs]
    have hm := mismatch_mapReceivedWord e.symm w (CPolynomial.mapCoeffs e q)
    rw [CPolynomial.mapCoeffs_symm] at hm
    exact ⟨hq'.1, hm ▸ hq'.2⟩
  · intro hp
    exact ⟨CPolynomial.mapCoeffs e.symm p, hc.mpr hp, CPolynomial.mapCoeffs_symm e.symm p⟩

end CompPoly.GuruswamiSudan
