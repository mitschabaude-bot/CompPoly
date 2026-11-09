/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Fold
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.TwiddleRow
/-! # Compact normalized-row additive transform plans -/
@[expose] public section
namespace AdditiveNTT.Bitsliced
open BF64

/-- Compact normalized rows and their three byte subset-sum tables. -/
structure Plan (β : Fin 64 → Word) (d : Nat) (hd : d < 64) where
  /-- Each stage retains its normalized row and fixed-size byte tables. -/
  stages : Vector (Sigma Packed.TwiddleRow) d
  /-- Compact lookup agrees with the generic encoder's twiddles. -/
  correct : ∀ (i : Fin d) (u : Fin (2 ^ (d - i.val - 1))),
    stages[i].2.lookup u.val = (Packed.stageTwiddles β d hd i).getD u.val 0

/-- Prepare one normalized row without enumerating its complete block domain. -/
def normalizedRow (β : Fin 64 → Word) (d : Nat) (hd : d < 64) (i : Fin d) :
    Packed.TwiddleRow (d - i.val - 1) :=
  let raw := computableNormalizedWValuesArray (ℓ := d) (R_rate := 0) β (by omega) i
  Packed.TwiddleRow.create _ ⟨raw, by
    simp only [raw, computableNormalizedWValuesArray, Array.size_ofFn, Nat.add_zero]⟩

/-- A compact normalized row recovers every generic additive-stage twiddle. -/
theorem normalizedRow_eq (β : Fin 64 → Word) (d : Nat) (hd : d < 64) (i : Fin d)
    (u : Fin (2 ^ (d - i.val - 1))) :
    (normalizedRow β d hd i).lookup u.val = (Packed.stageTwiddles β d hd i).getD u.val 0 := by
  rw [Packed.TwiddleRow.lookup_eq, Packed.rowSubset_eq]
  simp only [normalizedRow, Packed.TwiddleRow.create, Packed.stageTwiddles,
    computableTwiddleTableArray, Nat.add_zero, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn, u.isLt, ↓reduceDIte, Option.getD_some]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.getBit_eq_testBit]
  split <;> rfl

/-- Prepare compact normalized subspace rows and their byte tables. -/
def Plan.create (β : Fin 64 → Word) (d : Nat) (hd : d < 64) : Plan β d hd where
  stages := Vector.ofFn fun i => ⟨d - i.val - 1, normalizedRow β d hd i⟩
  correct i u := by
    have entry : (Vector.ofFn fun j : Fin d =>
        (⟨d - j.val - 1, normalizedRow β d hd j⟩ : Sigma Packed.TwiddleRow))[i.val] =
        ⟨d - i.val - 1, normalizedRow β d hd i⟩ := Vector.getElem_ofFn i.isLt
    exact (congrArg (fun row : Sigma Packed.TwiddleRow => row.2.lookup u.val) entry).trans
      (normalizedRow_eq β d hd i u)

/-- Read one scalar from a compact normalized row. -/
@[inline] def Plan.get (p : Plan β d hd) (i : Fin d)
    (u : Fin (2 ^ (d - i.val - 1))) : Word := p.stages[i].2.lookup u.val

/-- A compact scalar plan has the certified packed-plan interface. -/
def Plan.toPacked (p : Plan β d hd) : Packed.Plan β d hd where
  stages := Vector.ofFn fun i => Array.ofFn fun u => Packed.Multiplier.masked (p.get i u)
  stageSize i := by simp only [Vector.getElem_ofFn, Array.size_ofFn]
  scalar_eq i u := by
    simp only [Vector.getElem_ofFn, Array.getElem_ofFn, Packed.Multiplier.masked, Plan.get]
    exact p.correct i u

/-- Specification-plan scalar lookup recovers the compact scalar. -/
theorem Plan.scalar_toPacked (p : Plan β d hd) (i : Fin d) (u : Fin (2 ^ (d - i.val - 1))) :
    (p.toPacked.get i u).scalar = p.get i u := by
  simp only [Plan.toPacked, Packed.Plan.get, Vector.getElem_ofFn, Array.getElem_ofFn,
    Packed.Multiplier.masked]

end AdditiveNTT.Bitsliced
