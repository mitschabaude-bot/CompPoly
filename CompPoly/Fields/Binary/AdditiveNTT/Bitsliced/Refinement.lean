/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.StageProofs
/-! # Agreement of bit-plane stages with the certified packed stages -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace AdditiveNTT.Bitsliced
open BF64

/-- Row-major address of one coordinate in a padded row. -/
def wordIndex (r : Fin rows) (c : Fin 64) : Fin (rows * 64) :=
  ⟨r.val * 64 + c.val, by have := r.isLt; have := c.isLt; omega⟩

/-- The bit-plane representation and the packed representation have identical lanes. -/
def Represents (a b : BF64.Packed.Buffer (rows * 64)) : Prop :=
  ∀ r c, lane (readRow a r) c = BF64.Packed.read b (wordIndex r c)

/-- The row and coordinate partitions select the same packed word. -/
theorem stage_wordIndex (d : Nat) (i : Fin d) (j : PairIndex d i) (c : Fin 64) (b : Fin 2) :
    Packed.stageIndex d i 64 (finProdFinEquiv (j.1, finProdFinEquiv (j.2, c)), b) =
      wordIndex (rowPartition d i (j, b)) c := by
  let t : Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * 64)) :=
    finProdFinEquiv (j.1, finProdFinEquiv (j.2, c))
  have ht := finProdFinEquiv.symm_apply_apply (j.1, finProdFinEquiv (j.2, c))
  have hdiv : t.val / (2 ^ i.val * 64) = j.1.val := congrArg (fun p => p.1.val) ht
  have hmod : t.val % (2 ^ i.val * 64) = c.val + 64 * j.2.val :=
    congrArg (fun p => p.2.val) ht
  apply Fin.ext
  change t.val % (2 ^ i.val * 64) + (2 ^ i.val * 64) * b.val +
    (2 * (2 ^ i.val * 64)) * (t.val / (2 ^ i.val * 64)) =
      (rowPartition d i (j, b)).val * 64 + c.val
  rw [hdiv, hmod, rowPartition_val]
  ring

/-- The packed pair index retains its original scalar-block index. -/
theorem stage_divNat (d : Nat) (i : Fin d) (j : PairIndex d i) (c : Fin 64) :
    (finProdFinEquiv (j.1, finProdFinEquiv (j.2, c)) :
      Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * 64))).divNat = j.1 :=
  congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (j.1, finProdFinEquiv (j.2, c)))

/-- Read a row of the complete mathematical row stage. -/
theorem read_rowStage (p : Plan β d hd) (i : Fin d)
    (op : UInt64 → Block → Block → Block × Block) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) (j : PairIndex d i) (b : Fin 2) :
    readRow (rowStage p i op a hn) (rowPartition d i (j, b)) =
      if b = 0 then
        (op (BF64.Packed.read ⟨p.words[i.val], p.size_eq i⟩ j.1).val
          (readRow a (rowPartition d i (j, 0))) (readRow a (rowPartition d i (j, 1)))).1
      else
        (op (BF64.Packed.read ⟨p.words[i.val], p.size_eq i⟩ j.1).val
          (readRow a (rowPartition d i (j, 0))) (readRow a (rowPartition d i (j, 1)))).2 := by
  simp only [rowStage, read_rowSweep _ (rowPartition d i).injective hn _ _ _ (pairList_nodup d i),
    mem_pairList, ite_true]

/-- Refinement of a disjoint row stage follows from refinement of its butterfly. -/
theorem rowStage_represents (p : Plan β d hd) (i : Fin d)
    (op : UInt64 → Block → Block → Block × Block)
    (pair : Packed.Multiplier → Word → Word → Word × Word)
    (hop : ∀ m u v c, (lane (op m.scalar.val u v).1 c, lane (op m.scalar.val u v).2 c) =
      pair m (lane u c) (lane v c))
    (a b : Rows (2 ^ d)) (hab : Represents a b)
    (hn : 8 * (2 ^ d * 64) < 4294967296) :
    Represents (rowStage p i op a hn) (Packed.stageSweep p.toPacked i 64 pair b) := by
  intro r c
  obtain ⟨⟨j, side⟩, rfl⟩ := (rowPartition d i).surjective r
  rw [read_rowStage, Packed.stageSweep_eq_sweep, ← stage_wordIndex]
  rw [Packed.read_sweep _ (Packed.stageIndex d i 64).injective]
  simp only [stage_divNat]
  have hsource (s : Fin 2) :
      lane (readRow a (rowPartition d i (j, s))) c =
        BF64.Packed.read b (Packed.stageIndex d i 64
          (finProdFinEquiv (j.1, finProdFinEquiv (j.2, c)), s)) := by
    rw [stage_wordIndex]
    exact hab _ _
  have hpair := hop (p.toPacked.get i j.1)
    (readRow a (rowPartition d i (j, 0))) (readRow a (rowPartition d i (j, 1))) c
  rw [Plan.scalar_toPacked, hsource 0, hsource 1] at hpair
  fin_cases side
  · simpa using congrArg Prod.fst hpair
  · simpa using congrArg Prod.snd hpair

/-- The forward bit-plane stage refines the existing packed forward stage. -/
theorem forwardStage_represents (p : Plan β d hd) (i : Fin d) (a b : Rows (2 ^ d))
    (hab : Represents a b) (hn : 8 * (2 ^ d * 64) < 4294967296) :
    Represents (forwardStage p i a hn) (Packed.forwardStage p.toPacked i 64 b) := by
  rw [forwardStage, stageSweep_eq_rowStage _ _ forwardKernel_correct]
  exact rowStage_represents p i forwardOp Packed.forwardPair forwardOp_lane a b hab hn

/-- The inverse bit-plane stage refines the existing packed inverse stage. -/
theorem inverseStage_represents (p : Plan β d hd) (i : Fin d) (a b : Rows (2 ^ d))
    (hab : Represents a b) (hn : 8 * (2 ^ d * 64) < 4294967296) :
    Represents (inverseStage p i a hn) (Packed.inverseStage p.toPacked i 64 b) := by
  rw [inverseStage, stageSweep_eq_rowStage _ _ inverseKernel_correct]
  exact rowStage_represents p i inverseOp Packed.inversePair inverseOp_lane a b hab hn

/-- Related states remain related through matching finite traversals. -/
theorem finFold_rel {α β : Type*} (R : α → β → Prop)
    (f : α → Fin n → α) (g : β → Fin n → β)
    (h : ∀ a b j, R a b → R (f a j) (g b j)) (a : α) (b : β) (hab : R a b) :
    R (Fin.foldl n f a) (Fin.foldl n g b) := by
  have aux (xs : List (Fin n)) (a : α) (b : β) (hab : R a b) :
      R (xs.foldl f a) (xs.foldl g b) := by
    induction xs generalizing a b with
    | nil => exact hab
    | cons j xs ih => exact ih (f a j) (g b j) (h a b j hab)
  simp only [Fin.foldl_eq_finRange_foldl]
  exact aux _ a b hab

/-- The full descending bit-plane transform refines the packed transform. -/
theorem forward_represents (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d)
    (a b : Rows (2 ^ d)) (hab : Represents a b)
    (hn : 8 * (2 ^ d * 64) < 4294967296) :
    Represents (forward p ell hell a hn) (Packed.forward p.toPacked ell hell 64 b) := by
  unfold forward Packed.forward
  apply finFold_rel (Represents (rows := 2 ^ d)) _ _ _ a b hab
  intro a b k h
  exact forwardStage_represents p ⟨ell - k.val - 1, by omega⟩ a b h hn

/-- The full ascending inverse refines the packed inverse transform. -/
theorem inverse_represents (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d)
    (a b : Rows (2 ^ d)) (hab : Represents a b)
    (hn : 8 * (2 ^ d * 64) < 4294967296) :
    Represents (inverse p ell hell a hn) (Packed.inverse p.toPacked ell hell 64 b) := by
  unfold inverse Packed.inverse
  apply finFold_rel (Represents (rows := 2 ^ d)) _ _ _ a b hab
  intro a b k h
  exact inverseStage_represents p ⟨k.val, by omega⟩ a b h hn

/-- Inverse bit-plane encoding recovers every input lane. -/
theorem inverse_forward_lane (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d)
    (a b : Rows (2 ^ d)) (hab : Represents a b)
    (hn : 8 * (2 ^ d * 64) < 4294967296) (r : Fin (2 ^ d)) (c : Fin 64) :
    lane (readRow (inverse p ell hell (forward p ell hell a hn) hn) r) c =
      BF64.Packed.read b (wordIndex r c) := by
  exact (inverse_represents p ell hell _ _ (forward_represents p ell hell a b hab hn) hn r c).trans
    (Packed.read_inverse_forward p.toPacked ell hell 64 b (wordIndex r c))

end AdditiveNTT.Bitsliced
