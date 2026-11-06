/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Bivariate.GuruswamiSudan.Parameters
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan
public import CompPoly.Univariate.ReedSolomon.GaoTree
public import CompPoly.Univariate.SparseMul
public import CompPoly.Univariate.VanishingLinearized

/-! # Unique-radius decoding in the certified scalar decoder family -/

@[expose] public section

namespace CompPoly.GuruswamiSudan

/-- The distinct abscissas of a received word as a Reed–Solomon domain. -/
def receivedDomain {F : Type*} (w : GSReceivedWord F)
    (h : DistinctXCoordinates w.points) : ReedSolomon.Domain F :=
  ⟨w.points.map Prod.fst, by simpa only [Array.toList_map, DistinctXCoordinates] using h⟩

/-- The ordinates of a received word on its Reed–Solomon domain. -/
def receivedValues {F : Type*} (w : GSReceivedWord F)
    (h : DistinctXCoordinates w.points) : Vector F (receivedDomain w h).n :=
  ⟨w.points.map Prod.snd, by simp only [receivedDomain, ReedSolomon.Domain.n, Array.size_map]⟩

private theorem mismatch_fold_count {F : Type*} [Semiring F] [BEq F]
    (p : CPolynomial F) (xs : List (F × F)) (a : Nat) :
    xs.foldl (fun count point ↦ if p.eval point.1 == point.2 then count else count + 1) a =
      a + xs.countP (fun point ↦ !(p.eval point.1 == point.2)) := by
  induction xs generalizing a with
  | nil => simp only [List.foldl_nil, List.countP_nil, Nat.add_zero]
  | cons x xs ih =>
    simp only [List.foldl_cons, List.countP_cons]
    split <;> simp_all only [Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte] <;> omega

/-- The packed mismatch count is the Hamming distance used by Gao correctness. -/
theorem candidateMismatchCount_eq_hammingDist {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (w : GSReceivedWord F) (h : DistinctXCoordinates w.points) {k : Nat}
    (msg : Vector F k) :
    candidateMismatchCount w.points (ReedSolomon.messagePoly msg) =
      hammingDist (receivedValues w h).get (ReedSolomon.encode (receivedDomain w h) msg).get := by
  have hv (i : Fin (receivedDomain w h).n) :
      (receivedValues w h).get i = (w.points[i.val]'(by
        simpa only [receivedDomain, ReedSolomon.Domain.n, Array.size_map] using i.isLt)).2 := by
    simp only [receivedValues, Vector.get, Array.getElem_map]
    rfl
  have hx (i : Fin (receivedDomain w h).n) :
      (receivedDomain w h).val[i] = (w.points[i.val]'(by
        simpa only [receivedDomain, ReedSolomon.Domain.n, Array.size_map] using i.isLt)).1 := by
    exact Array.getElem_map ..
  rw [candidateMismatchCount, ← Array.foldl_toList, mismatch_fold_count, Nat.zero_add,
    hammingDist]
  simp only [ReedSolomon.encode_get, hv, hx]
  rw [← List.toFinset_finRange, (List.nodup_finRange _).card_eq_countP]
  rw [← List.ofFn_getElem (xs := w.points.toList), List.ofFn_eq_map, List.countP_map]
  have hn : w.points.size = (receivedDomain w h).n := by
    simp only [receivedDomain, ReedSolomon.Domain.n, Array.size_map]
  have hr {n m : Nat} (heq : n = m) :
      (List.finRange n).map (Fin.cast heq) = List.finRange m := by
    subst m
    have hf : Fin.cast (rfl : n = n) = id := by
      funext x
      exact Fin.ext rfl
    rw [hf, List.map_id]
  rw [← hr hn, List.countP_map]
  congr 1
  funext i
  simp only [Function.comp_def, Array.getElem_toList, Fin.val_cast]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq, ne_comm]

/-- Gao's singleton, restricted to the requested distance cutoff. -/
def decodeUnique {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (k e : Nat) (w : GSReceivedWord F) : Array (CPolynomial F) :=
  if h : distinctXCoordinatesBool w.points = true then
    let hd := LeeOSullivan.distinctXCoordinatesBool_iff.mp h
    (ReedSolomon.Gao.decodeTree CPolynomial.MulContext.skipZeros
      (CPolynomial.VanishingPolynomialContext.linearized CPolynomial.MulContext.skipZeros)
      k (receivedDomain w hd) (receivedValues w hd)).toArray.filter
      (passesCandidateDistance w.points e)
  else #[]

/-- Exact coverage at every cutoff inside the unique decoding radius. -/
theorem mem_decodeUnique_iff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (k e : Nat) (w : GSReceivedWord F) (hkn : k < w.length)
    (he : 2 * e ≤ w.length - k) (hd : DistinctXCoordinates w.points)
    (p : CPolynomial F) :
    p ∈ (decodeUnique k e w).toList ↔
      degreeLt p k ∧ candidateMismatchCount w.points p ≤ e := by
  have hn : (receivedDomain w hd).n = w.length := by
    simp only [receivedDomain, ReedSolomon.Domain.n, Array.size_map, GSReceivedWord.length]
  have hkn' : k < (receivedDomain w hd).n := hn ▸ hkn
  have hb := LeeOSullivan.distinctXCoordinatesBool_iff.mpr hd
  simp only [decodeUnique, dite_eq_left hb, ReedSolomon.Gao.decodeTree_eq_decode,
    Array.toList_filter, List.mem_filter,
    Option.toList_toArray, Option.mem_toList, passesCandidateDistance_iff]
  constructor
  · rintro ⟨hp, hdist⟩
    obtain ⟨msg, hmsg, _⟩ := ReedSolomon.Gao.decode_sound k (receivedDomain w hd)
      (receivedValues w hd) hkn' p hp
    exact ⟨hmsg ▸ ReedSolomon.messagePoly_degree_lt msg, hdist⟩
  · rintro ⟨hdeg, hdist⟩
    let msg := Vector.ofFn fun i : Fin k ↦ p.coeff i
    have hm : ReedSolomon.messagePoly msg = p := ReedSolomon.messagePoly_ofFn_coeff k p hdeg
    refine ⟨?_, hdist⟩
    rw [← hm]
    apply ReedSolomon.Gao.decode_eq_some k (receivedDomain w hd) (receivedValues w hd) hkn' msg
    rw [← candidateMismatchCount_eq_hammingDist, hm]
    rw [hn]
    exact (Nat.mul_le_mul_left 2 hdist).trans he

/-- Select unique decoding exactly when the requested cutoff lies inside its radius. -/
def decodeWithUnique {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ctx : GSFilteredCoreContext F) (k e : Nat) (w : GSReceivedWord F) :
    Array (CPolynomial F) :=
  match finiteGSParamSelector.choose k w.length e with
  | none => #[]
  | some params =>
    if k < w.length ∧ 2 * e ≤ w.length - k then decodeUnique k e w
    else decodeWithParams ctx params w

/-- The family covers exactly the requested ball, independently of the selected backend. -/
theorem mem_decodeWithUnique_iff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ctx : GSFilteredCoreContext F) {k e : Nat} (w : GSReceivedWord F)
    {params : GSExecParams}
    (hselect : finiteGSParamSelector.choose k w.length e = some params)
    (hd : DistinctXCoordinates w.points) (p : CPolynomial F) :
    p ∈ (decodeWithUnique ctx k e w).toList ↔
      degreeLt p k ∧ candidateMismatchCount w.points p ≤ e := by
  simp only [decodeWithUnique, hselect]
  split
  · rename_i h
    exact mem_decodeUnique_iff k e w h.1 h.2 hd p
  · simpa only [decode, hselect] using
      mem_decode_finiteGSParamSelector_iff ctx w hselect hd p

end CompPoly.GuruswamiSudan
