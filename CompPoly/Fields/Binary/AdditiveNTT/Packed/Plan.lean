/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Butterfly
public import CompPoly.Fields.Binary.AdditiveNTT.Executable
public import CompPoly.Fields.Binary.BF64.WordField

/-!
# Reusable polynomial-basis additive NTT plans

Plans retain stage twiddles and prepare byte maps for the first eight layers.
The remaining layers use masked word multiplication. A plan is independent of
the lane count and encoding rate, and serves both forward and inverse sweeps.
-/

@[expose] public section

namespace AdditiveNTT.Packed

open BF64

/-- The fixed flat binary basis, with bit `i` representing `X^i`. -/
def flatBasis (i : Fin 64) : Word := ⟨(1 : UInt64) <<< UInt64.ofNat i.val⟩

/-- Twiddles for all blocks of one normalized additive stage. -/
def stageTwiddles (β : Fin 64 → Word) (d : Nat) (hd : d < 64) (i : Fin d) : Array Word :=
  computableTwiddleTableArray (ℓ := d) (R_rate := 0) β (by omega) i

/-- Build binary subset sums by sharing the lower half of each successive table. -/
def subsetSums {R : Type} [AddCommMonoid R] (values : Array R) : Nat → Array R
  | 0 => #[0]
  | n+1 =>
    let low := subsetSums values n
    low ++ low.map (fun x => x + values.getD n 0)

/-- A subset table has one entry for every binary mask. -/
@[simp] theorem subsetSums_size {R : Type} [AddCommMonoid R] (values : Array R) (n : Nat) :
    (subsetSums values n).size = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [subsetSums, Array.size_append, Array.size_map, ih, pow_succ]; omega

/-- Each shared table entry is the sum selected by its binary mask. -/
theorem subsetSums_get {R : Type} [AddCommMonoid R] (values : Array R) (n u : Nat)
    (hu : u < 2^n) :
    (subsetSums values n)[u]'(by rw [subsetSums_size]; exact hu) =
      ∑ k : Fin n, if u.testBit k.val then values.getD k.val 0 else 0 := by
  induction n generalizing u with
  | zero =>
    have : u = 0 := by simp only [pow_zero] at hu; omega
    subst u
    simp only [subsetSums, Array.getElem_singleton, Fin.sum_univ_zero]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    by_cases low : u < 2^n
    · have bit : u.testBit n = false := Nat.testBit_lt_two_pow low
      simp only [subsetSums]
      rw [Array.getElem_append_left (by rw [subsetSums_size]; exact low)]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, add_zero, Fin.val_castSucc, Fin.val_last]
      exact ih u low
    · have bound : u - 2^n < 2^n := by rw [pow_succ] at hu; omega
      have split : u = 2^n + (u-2^n) := by omega
      have bit : u.testBit n = true := by
        rw [split, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow bound]; rfl
      have bits (k : Fin n) : u.testBit k.val = (u-2^n).testBit k.val := by
        conv_lhs => rw [split]
        exact Nat.testBit_two_pow_add_gt k.isLt _
      simp only [subsetSums]
      rw [Array.getElem_append_right (by rw [subsetSums_size]; omega)]
      simp only [Array.getElem_map, subsetSums_size, ih (u-2^n) bound, Fin.val_castSucc,
        Fin.val_last, bit, ↓reduceIte, bits]

/-- Prepare one additive stage with linear work in its number of twiddles. -/
def stageTwiddlesShared (β : Fin 64 → Word) (d : Nat) (hd : d < 64) (i : Fin d) : Array Word :=
  subsetSums (computableNormalizedWValuesArray (ℓ := d) (R_rate := 0) β (by omega) i)
    (d-i.val-1)

/-- Shared subset sums retain every normalized additive-stage twiddle. -/
@[csimp] theorem stageTwiddles_code : stageTwiddles = stageTwiddlesShared := by
  funext β d hd i
  apply Array.ext
  · simp only [stageTwiddles, stageTwiddlesShared, subsetSums_size,
      computableTwiddleTableArray, Array.size_ofFn, Nat.add_zero]
  · intro u hu hv
    simp only [stageTwiddlesShared, subsetSums_get _ _ u (by
      simpa only [stageTwiddles, computableTwiddleTableArray, Array.size_ofFn,
        Nat.add_zero] using hu),
      stageTwiddles, computableTwiddleTableArray, Array.getElem_ofFn, Nat.add_zero]
    apply Finset.sum_congr rfl
    intro k _
    simp only [← Nat.testBit_true_eq_getBit_eq_1]

/-- Cached multipliers indexed by the descending stage number. -/
structure Plan (β : Fin 64 → Word) (d : Nat) (hd : d < 64) where
  /-- One multiplier array per stage, stage zero pairing adjacent rows. -/
  stages : Vector (Array Multiplier) d
  /-- Every stage has one multiplier for each row block. -/
  stageSize : ∀ i : Fin d, stages[i.val].size = 2 ^ (d - i.val - 1)
  /-- Every retained multiplier has the generic encoder's twiddle. -/
  scalar_eq : ∀ (i : Fin d) (u : Fin (2 ^ (d - i.val - 1))),
    (stages[i.val][u.val]'(by rw [stageSize]; exact u.isLt)).scalar =
      (stageTwiddles β d hd i).getD u.val 0

/-- Prepare a plan once, outside all timed transforms using it. -/
def Plan.create (β : Fin 64 → Word) (d : Nat) (hd : d < 64) : Plan β d hd where
  stages := Vector.ofFn fun i =>
    let raw := stageTwiddles β d hd i
    Array.ofFn fun u : Fin (2 ^ (d - i.val - 1)) =>
      let t := raw.getD u.val 0
      if d - i.val - 1 < 8 then Multiplier.prepared t else Multiplier.masked t
  stageSize i := by simp only [Vector.getElem_ofFn, Array.size_ofFn]
  scalar_eq i u := by
    simp only [Vector.getElem_ofFn, Array.getElem_ofFn]
    split <;> rfl

/-- Read a certified stage multiplier. -/
@[inline] def Plan.get (p : Plan β d hd) (i : Fin d)
    (u : Fin (2 ^ (d - i.val - 1))) : Multiplier :=
  p.stages[i.val][u.val]'(by rw [p.stageSize]; exact u.isLt)

/-- Every cached multiplication agrees with the generic stage twiddle. -/
theorem Plan.get_correct (p : Plan β d hd) (i : Fin d)
    (u : Fin (2 ^ (d - i.val - 1))) (a : Word) :
    ((p.get i u).apply a).toField =
      ((stageTwiddles β d hd i).getD u.val 0).toField * a.toField := by
  rw [(p.get i u).correct]
  exact congrArg (fun t : Word => t.toField * a.toField) (p.scalar_eq i u)

/-- A plan over leanVM's flat polynomial basis. -/
abbrev FlatPlan (d : Nat) (hd : d < 64) := Plan flatBasis d hd

end AdditiveNTT.Packed
