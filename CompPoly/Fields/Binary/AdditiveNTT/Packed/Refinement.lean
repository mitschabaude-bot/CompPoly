/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Correctness
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.IndexLemmas

/-! # Refinement of packed sweeps to the generic additive encoder -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace AdditiveNTT.Packed

open BF64

/-- One lane of a packed row-major buffer, as a function of row indices. -/
def laneView (a : BF64.Packed.Buffer (rows * lanes)) (lane : Fin lanes) : Fin rows → Word :=
  fun row => BF64.Packed.read a (finProdFinEquiv (row, lane))

private theorem array_ofFn_getD {A : Type*} [Zero A] {n : Nat}
    (f : Fin n → A) (i : Fin n) : (Array.ofFn f).getD i.val 0 = f i := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, i.isLt,
    dite_true, Option.getD_some]

/-- The generic array stage acts on the same disjoint row pairs as the packed sweep. -/
theorem arrayStage_pair (d : Nat) (i : Fin d) (twiddles : Array Word)
    (f : Fin (2 ^ d) → Word) (u : Fin (2 ^ (d - i.val - 1)))
    (v : Fin (2 ^ i.val)) (b : Fin 2) :
    arrayToFinFunction (2 ^ d)
      (computableNTTStageArray (ℓ := d) (R_rate := 0) i twiddles (Array.ofFn f))
      (rowIndex d i (finProdFinEquiv (u, v), b)) =
      if b = 0 then
        f (rowIndex d i (finProdFinEquiv (u, v), 0)) +
          twiddles.getD u.val 0 * f (rowIndex d i (finProdFinEquiv (u, v), 1))
      else
        f (rowIndex d i (finProdFinEquiv (u, v), 0)) +
          (twiddles.getD u.val 0 + 1) * f (rowIndex d i (finProdFinEquiv (u, v), 1)) := by
  unfold arrayToFinFunction computableNTTStageArray
  simp only [Nat.add_zero, array_ofFn_getD]
  rw [rowIndex_div]
  have hb := b.isLt
  have hdiv : (b.val + 2 * u.val) / 2 = u.val := by omega
  have hmod : (b.val + 2 * u.val) % 2 = b.val := by omega
  rw [hdiv, hmod]
  fin_cases b
  · simp only [Fin.mk_zero, dite_true, ite_true]
    rw [← rowIndex_one]
    rw [array_ofFn_getD]
  · simp only [Fin.mk_one, one_ne_zero, dite_false, ite_false, rowIndex_xor]
    rw [array_ofFn_getD]

/-- The packed butterfly is the generic normalized field butterfly on words. -/
theorem forwardPair_eq (m : Multiplier) (u v : Word) :
    forwardPair m u v = (u + m.scalar * v, u + (m.scalar + 1) * v) := by
  have h := forwardPair_toField m u v
  apply Prod.ext
  · apply Word.toField_injective
    change (forwardPair m u v).1.toField = Word.ringEquiv (u + m.scalar * v)
    rw [map_add, map_mul]
    exact congrArg Prod.fst h
  · apply Word.toField_injective
    change (forwardPair m u v).2.toField = Word.ringEquiv (u + (m.scalar + 1) * v)
    rw [map_add, map_mul, map_add, map_one]
    exact congrArg Prod.snd h

/-- Each packed stage agrees with the generic array stage independently in every lane. -/
theorem laneView_forwardStage (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) (lane : Fin lanes) :
    laneView (forwardStage p i lanes a) lane =
      arrayToFinFunction (2 ^ d)
        (computableNTTStageArray (ℓ := d) (R_rate := 0) i
          (stageTwiddles β d hd i) (Array.ofFn (laneView a lane))) := by
  funext row
  obtain ⟨⟨t, b⟩, rfl⟩ := (rowIndex d i).surjective row
  obtain ⟨⟨u, v⟩, rfl⟩ := finProdFinEquiv.surjective t
  rw [arrayStage_pair]
  unfold laneView
  rw [← stageIndex_lane]
  simp only [forwardStage_eq_sweep, read_sweep _ (stageIndex d i lanes).injective]
  have hdiv : (finProdFinEquiv (u, finProdFinEquiv (v, lane))).divNat = u :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)
  rw [hdiv, forwardPair_eq]
  simp only [Plan.get, p.scalar_eq]
  rw [stageIndex_lane, stageIndex_lane]

section Generic

variable {β : Fin 64 → Word}

variable {F : Type} [Field F] [Fintype F] [Fact (Fintype.card F = 2)]
variable [Fact (Nat.Prime (ringChar F))] [Algebra F Word]
variable [Fintype Word] [Fact (LinearIndependent F β)]

omit [Fintype Word] in
private theorem constantsLoop_independent (β : Fin 64 → Word)
    (ell₁ rate₁ ell₂ rate₂ : Nat) (i : Fin 64) (k : Nat) (c : Array Word) :
    subspacePolynomialConstantsArrayLoop (ℓ := ell₁) (R_rate := rate₁) β i k c =
      subspacePolynomialConstantsArrayLoop (ℓ := ell₂) (R_rate := rate₂) β i k c := by
  rw [subspacePolynomialConstantsArrayLoop, subspacePolynomialConstantsArrayLoop]
  split
  · exact constantsLoop_independent β ell₁ rate₁ ell₂ rate₂ i (k + 1) _
  · rfl
termination_by i.val - k

omit [Fintype Word] in
private theorem stageTwiddles_eq {ell rate : Nat} (hd : ell + rate < 64)
    (i : Fin ell) :
    stageTwiddles β (ell + rate) hd ⟨i.val, by omega⟩ =
      computableTwiddleTableArray (ℓ := ell) (R_rate := rate) β hd i := by
  simp only [stageTwiddles, computableTwiddleTableArray,
    computableNormalizedWValuesArray, Nat.add_zero]
  have hc : subspacePolynomialConstantsArray (ℓ := ell + rate) (R_rate := 0)
      β ⟨i.val, by omega⟩ =
      subspacePolynomialConstantsArray (ℓ := ell) (R_rate := rate) β ⟨i.val, by omega⟩ :=
    constantsLoop_independent β (ell + rate) 0 ell rate _ 0 #[]
  rw [hc]

/-- A packed stage is the generic additive encoder's stage on every lane. -/
theorem laneView_forwardStage_eq_generic {ell rate : Nat} (hd : ell + rate < 64)
    (p : Plan β (ell + rate) hd) (i : Fin ell) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ (ell + rate) * lanes)) (lane : Fin lanes) :
    laneView (forwardStage p ⟨i.val, by omega⟩ lanes a) lane =
      computableNTTStage (𝔽q := F) β hd i (laneView a lane) := by
  rw [laneView_forwardStage, stageTwiddles_eq hd i]
  have hs (tw : Array Word) (b : Array Word) :
      computableNTTStageArray (ℓ := ell + rate) (R_rate := 0)
        ⟨i.val, by omega⟩ tw b =
      computableNTTStageArray (ℓ := ell) (R_rate := rate) i tw b := by
    simp only [computableNTTStageArray, Nat.add_zero]
  rw [hs, computableNTTStageArray_eq_computableNTTStage (𝔽q := F) β hd i]
  congr 1
  funext j
  exact array_ofFn_getD _ j

/-- The packed driver refines the generic descending-stage fold, lane by lane. -/
theorem laneView_forward_eq_fold {ell rate : Nat} (hd : ell + rate < 64)
    (p : Plan β (ell + rate) hd) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ (ell + rate) * lanes)) (lane : Fin lanes) :
    laneView (forward p ell (by omega) lanes a) lane =
      Fin.foldl ell (fun f k => computableNTTStage (𝔽q := F) β hd
        ⟨ell - k.val - 1, by omega⟩ f) (laneView a lane) := by
  unfold forward
  simp only [Fin.foldl_eq_finRange_foldl]
  apply (List.foldl_hom (fun a => laneView a lane) _).symm
  intro a k
  exact (laneView_forwardStage_eq_generic (F := F) hd p _ lanes a lane).symm

end Generic

end AdditiveNTT.Packed
