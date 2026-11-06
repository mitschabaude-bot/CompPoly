/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Transform
public import CompPoly.Fields.Binary.AdditiveNTT.Correctness

/-! # Stage refinements and inverse correctness for packed additive NTTs -/

@[expose] public section

namespace AdditiveNTT.Packed

open BF64

private theorem add_cancel_left (u v : Word) : Word.add u (Word.add u v) = v := by
  cases u
  cases v
  simp only [Word.add, ← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]

private theorem add_cancel_right (u v : Word) : Word.add (Word.add u v) v = u := by
  cases u
  cases v
  simp only [Word.add, UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero]

/-- The inverse butterfly recovers both inputs, including a zero twiddle. -/
@[simp] theorem inversePair_forwardPair (m : Multiplier) (u v : Word) :
    inversePair m (forwardPair m u v).1 (forwardPair m u v).2 = (u, v) := by
  simp only [inversePair, forwardPair, add_cancel_left, add_cancel_right]

/-- The forward butterfly recovers both inverse inputs. -/
@[simp] theorem forwardPair_inversePair (m : Multiplier) (u v : Word) :
    forwardPair m (inversePair m u v).1 (inversePair m u v).2 = (u, v) := by
  simp only [inversePair, forwardPair, add_cancel_right, add_cancel_left]

/-- A forward pair agrees with the normalized field butterfly. -/
theorem forwardPair_toField (m : Multiplier) (u v : Word) :
    ((forwardPair m u v).1.toField, (forwardPair m u v).2.toField) =
      (u.toField + m.scalar.toField * v.toField,
        u.toField + (m.scalar.toField + 1) * v.toField) := by
  simp only [forwardPair, Word.toField_add, m.correct]
  congr 1
  rw [add_mul, one_mul, add_assoc]

/-- Reading the inverse of a forward stage recovers the input coordinate. -/
theorem read_inverseStage_forwardStage (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) (j : Fin (2 ^ d * lanes)) :
    BF64.Packed.read (inverseStage p i lanes (forwardStage p i lanes a)) j =
      BF64.Packed.read a j := by
  obtain ⟨⟨t, b⟩, rfl⟩ := (stageIndex d i lanes).surjective j
  simp only [inverseStage_eq_sweep, read_sweep _ (stageIndex d i lanes).injective,
    forwardStage_eq_sweep]
  simp only [ite_true, show ¬(1 : Fin 2) = 0 from by decide, ite_false]
  have h := inversePair_forwardPair (p.get i (finProdFinEquiv.symm t).1)
    (BF64.Packed.read a ((stageIndex d i lanes) (t, 0)))
    (BF64.Packed.read a ((stageIndex d i lanes) (t, 1)))
  fin_cases b
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Pointwise-equal inputs have pointwise-equal inverse stages. -/
theorem inverseStage_congr (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (a b : BF64.Packed.Buffer (2 ^ d * lanes))
    (hab : ∀ j, BF64.Packed.read a j = BF64.Packed.read b j)
    (j : Fin (2 ^ d * lanes)) :
    BF64.Packed.read (inverseStage p i lanes a) j =
      BF64.Packed.read (inverseStage p i lanes b) j := by
  obtain ⟨⟨t, s⟩, rfl⟩ := (stageIndex d i lanes).surjective j
  simp only [inverseStage_eq_sweep, read_sweep _ (stageIndex d i lanes).injective, hab]

/-- The forward driver peels off its highest stage first. -/
theorem forward_succ (p : Plan β d hd) (ell : Nat) (hell : ell + 1 ≤ d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    forward p (ell + 1) hell lanes a =
      forward p ell (by omega) lanes (forwardStage p ⟨ell, by omega⟩ lanes a) := by
  unfold forward
  rw [Fin.foldl_succ]
  congr 1
  funext a k
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

/-- The inverse driver peels off its highest stage last. -/
theorem inverse_succ (p : Plan β d hd) (ell : Nat) (hell : ell + 1 ≤ d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    inverse p (ell + 1) hell lanes a =
      inverseStage p ⟨ell, by omega⟩ lanes (inverse p ell (by omega) lanes a) := by
  unfold inverse
  rw [Fin.foldl_succ_last]
  rfl

/-- Inverse encoding recovers every tiled novel coefficient in every lane. -/
theorem read_inverse_forward (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (a : BF64.Packed.Buffer (2 ^ d * lanes)) (j : Fin (2 ^ d * lanes)) :
    BF64.Packed.read (inverse p ell hell lanes (forward p ell hell lanes a)) j =
      BF64.Packed.read a j := by
  induction ell generalizing a j with
  | zero => rfl
  | succ ell ih =>
    rw [forward_succ, inverse_succ]
    have hrec (k : Fin (2 ^ d * lanes)) :=
      ih (by omega) (forwardStage p ⟨ell, by omega⟩ lanes a) k
    have hstage := inverseStage_congr p ⟨ell, by omega⟩ lanes
      (inverse p ell (by omega) lanes
        (forward p ell (by omega) lanes (forwardStage p ⟨ell, by omega⟩ lanes a)))
      (forwardStage p ⟨ell, by omega⟩ lanes a) hrec j
    exact hstage.trans (read_inverseStage_forwardStage p ⟨ell, by omega⟩ lanes a j)

end AdditiveNTT.Packed
