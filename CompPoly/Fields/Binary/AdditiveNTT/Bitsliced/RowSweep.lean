/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.NativeProofs
/-! # Disjoint butterfly sweeps over packed bit-plane rows -/
@[expose] public section
namespace AdditiveNTT.Bitsliced

/-- Update a pair of entire bit-plane rows. -/
def updateRows (index : J × Fin 2 → Fin rows) (hn : 8 * (rows * 64) < 4294967296)
    (op : J → Block → Block → Block × Block) (a : BF64.Packed.Buffer (rows * 64))
    (j : J) : BF64.Packed.Buffer (rows * 64) :=
  let out := op j (readRow a (index (j, 0))) (readRow a (index (j, 1)))
  writeRow (writeRow a hn (index (j, 0)) out.1) hn (index (j, 1)) out.2

/-- One disjoint row update reads only the row's own pair. -/
theorem read_updateRows [DecidableEq J] (index : J × Fin 2 → Fin rows)
    (hinj : Function.Injective index) (hn : 8 * (rows * 64) < 4294967296)
    (op : J → Block → Block → Block × Block) (a : BF64.Packed.Buffer (rows * 64))
    (j t : J) (b : Fin 2) :
    readRow (updateRows index hn op a j) (index (t, b)) =
      if j = t then
        if b = 0 then (op t (readRow a (index (t, 0))) (readRow a (index (t, 1)))).1
        else (op t (readRow a (index (t, 0))) (readRow a (index (t, 1)))).2
      else readRow a (index (t, b)) := by
  simp only [updateRows, readRow_writeRow, hinj.eq_iff, Prod.mk.injEq]
  by_cases h : j = t
  · subst j
    fin_cases b <;> simp
  · simp only [h, false_and, ite_false]

/-- A sweep over distinct row pairs reads both operands from the input buffer. -/
theorem read_rowSweep [DecidableEq J] (index : J × Fin 2 → Fin rows)
    (hinj : Function.Injective index) (hn : 8 * (rows * 64) < 4294967296)
    (op : J → Block → Block → Block × Block) (a : BF64.Packed.Buffer (rows * 64))
    (xs : List J) (hx : xs.Nodup) (t : J) (b : Fin 2) :
    readRow (xs.foldl (updateRows index hn op) a) (index (t, b)) =
      if t ∈ xs then
        if b = 0 then (op t (readRow a (index (t, 0))) (readRow a (index (t, 1)))).1
        else (op t (readRow a (index (t, 0))) (readRow a (index (t, 1)))).2
      else readRow a (index (t, b)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons j xs ih =>
    rw [List.nodup_cons] at hx
    rw [List.foldl_cons, ih _ hx.2]
    by_cases hj : j = t
    · subst j
      simp only [hx.1, ite_false, List.mem_cons, true_or, ite_true]
      simpa only [ite_true] using read_updateRows index hinj hn op a t t b
    · simp only [read_updateRows index hinj hn, hj, ite_false]
      simp only [List.mem_cons, Ne.symm hj, false_or]

/-- Projection commutes with a fold whose step refines the projected step. -/
theorem foldl_projection (xs : List J) (f : α → β) (step : α → J → α)
    (spec : β → J → β) (h : ∀ a j, f (step a j) = spec (f a) j) (a : α) :
    f (xs.foldl step a) = xs.foldl spec (f a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons j xs ih => rw [List.foldl_cons, List.foldl_cons, ih, h]

/-- Projection through an indexed finite traversal. -/
theorem finFold_projection {α β : Type*} (f : α → β) (step : α → Fin n → α)
    (spec : β → Fin n → β) (h : ∀ a j, f (step a j) = spec (f a) j) (a : α) :
    f (Fin.foldl n step a) = Fin.foldl n spec (f a) := by
  simp only [Fin.foldl_eq_finRange_foldl]
  exact foldl_projection _ f step spec h a

end AdditiveNTT.Bitsliced
