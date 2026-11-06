/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Fold
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Plan
/-! # Packed scalar-only additive transform plans -/
@[expose] public section
namespace AdditiveNTT.Bitsliced
open BF64

/-- Retained scalar words, without per-scalar multiplication closures or byte maps. -/
structure Plan (β : Fin 64 → Word) (d : Nat) (hd : d < 64) where
  /-- Stage zero pairs adjacent rows. -/
  words : Vector BF64.Packed d
  /-- The scalar count of each stage. -/
  size_eq : ∀ i : Fin d, words[i.val].size = 2 ^ (d - i.val - 1)
  /-- Retained words are the generic encoder's twiddles. -/
  correct : ∀ i u, BF64.Packed.read ⟨words[i.val], size_eq i⟩ u =
    (Packed.stageTwiddles β d hd i).getD u.val 0

/-- Materialize each scalar table in contiguous bytes. -/
def Plan.create (β : Fin 64 → Word) (d : Nat) (hd : d < 64) : Plan β d hd :=
  let tables := Vector.ofFn fun i : Fin d =>
    let raw := Packed.stageTwiddles β d hd i
    (Packed.tabulate (2 ^ (d - i.val - 1)) fun u => raw.getD u.val 0).val
  { words := tables
    size_eq := fun i => by
      simp only [tables, Vector.getElem_ofFn]
      exact (Packed.tabulate _ _).property
    correct := fun i u => by
      simp only [tables, Vector.getElem_ofFn]
      exact Packed.read_tabulate _ _ u }

/-- A scalar plan has the existing certified packed-plan interface. -/
def Plan.toPacked (p : Plan β d hd) : Packed.Plan β d hd where
  stages := Vector.ofFn fun i => Array.ofFn fun u =>
    Packed.Multiplier.masked (BF64.Packed.read ⟨p.words[i.val], p.size_eq i⟩ u)
  stageSize i := by simp only [Vector.getElem_ofFn, Array.size_ofFn]
  scalar_eq i u := by
    simp only [Vector.getElem_ofFn, Array.getElem_ofFn, Packed.Multiplier.masked]
    exact p.correct i u

/-- Specification-plan scalar lookup recovers the packed scalar. -/
theorem Plan.scalar_toPacked (p : Plan β d hd) (i : Fin d) (u : Fin (2 ^ (d - i.val - 1))) :
    (p.toPacked.get i u).scalar = BF64.Packed.read ⟨p.words[i.val], p.size_eq i⟩ u := by
  simp only [Plan.toPacked, Packed.Plan.get, Vector.getElem_ofFn, Array.getElem_ofFn,
    Packed.Multiplier.masked]

end AdditiveNTT.Bitsliced
