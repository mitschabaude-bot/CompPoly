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
