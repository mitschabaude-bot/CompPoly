/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Plan

/-!
# Batched packed forward and inverse additive transforms

Rows are contiguous and each row contains independent K words. An E lane is
three consecutive K words, so the same sweeps preserve its ordered limbs.
-/

@[expose] public section

namespace AdditiveNTT.Packed

open BF64

/-- Rearrange `(pair, side)` into blocks with a lower and an upper half. -/
def pairIndex (blocks span : Nat) :
    Fin (blocks * span) × Fin 2 ≃ Fin (blocks * (2 * span)) where
  toFun p :=
    let q := finProdFinEquiv.symm p.1
    finProdFinEquiv (q.1, finProdFinEquiv (p.2, q.2))
  invFun j :=
    let q := finProdFinEquiv.symm j
    let r := finProdFinEquiv.symm q.2
    (finProdFinEquiv (q.1, r.2), r.1)
  left_inv p := by simp only [Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv j := by simp only [Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]

/-- Number of packed words in a row block of stage `i`. -/
theorem stage_word_count (d : Nat) (i : Fin d) (lanes : Nat) :
    2 ^ (d - i.val - 1) * (2 * (2 ^ i.val * lanes)) = 2 ^ d * lanes := by
  have he : d - i.val - 1 + (i.val + 1) = d := by omega
  calc
    _ = (2 ^ (d - i.val - 1) * 2 ^ (i.val + 1)) * lanes := by
      rw [pow_succ]
      ac_rfl
    _ = _ := by rw [← pow_add, he]

/-- The pair partition of one batched stage. -/
@[inline] def stageIndex (d : Nat) (i : Fin d) (lanes : Nat) :
    Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes)) × Fin 2 ≃
      Fin (2 ^ d * lanes) :=
  let e := (pairIndex (2 ^ (d - i.val - 1)) (2 ^ i.val * lanes)).trans
    (finCongr (stage_word_count d i lanes))
  { toFun := fun p => ⟨p.1.val % (2 ^ i.val * lanes) + (2 ^ i.val * lanes) * p.2.val +
        (2 * (2 ^ i.val * lanes)) * (p.1.val / (2 ^ i.val * lanes)), (e p).isLt⟩
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

/-- The arithmetic address calculation is the block-and-side permutation. -/
theorem stageIndex_apply (d : Nat) (i : Fin d) (lanes : Nat)
    (p : Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes)) × Fin 2) :
    stageIndex d i lanes p =
      ((pairIndex _ _).trans (finCongr (stage_word_count d i lanes))) p := rfl

/-- Lower address of a disjoint packed butterfly. -/
@[inline] def lowerIndex (d : Nat) (i : Fin d) (lanes : Nat)
    (j : Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes))) : Fin (2 ^ d * lanes) :=
  ⟨j.val % (2 ^ i.val * lanes) + (2 * (2 ^ i.val * lanes)) * (j.val / (2 ^ i.val * lanes)), by
    have h := ((stageIndex d i lanes) (j, 0)).isLt
    change j.val % (2 ^ i.val * lanes) + (2 ^ i.val * lanes) * 0 +
      (2 * (2 ^ i.val * lanes)) * (j.val / (2 ^ i.val * lanes)) < _ at h
    simpa only [Nat.mul_zero, Nat.add_zero] using h⟩

/-- Upper address, one stride after the lower address. -/
@[inline] def upperIndex (d : Nat) (i : Fin d) (lanes : Nat)
    (j : Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes))) : Fin (2 ^ d * lanes) :=
  ⟨(lowerIndex d i lanes j).val + 2 ^ i.val * lanes, by
    have h := ((stageIndex d i lanes) (j, 1)).isLt
    change j.val % (2 ^ i.val * lanes) + (2 ^ i.val * lanes) * 1 +
      (2 * (2 ^ i.val * lanes)) * (j.val / (2 ^ i.val * lanes)) < _ at h
    change j.val % (2 ^ i.val * lanes) +
      (2 * (2 ^ i.val * lanes)) * (j.val / (2 ^ i.val * lanes)) +
      2 ^ i.val * lanes < _
    omega⟩

/-- Arithmetic-indexed stage sweep with a shared multiplier per row block. -/
@[specialize] def stageSweep (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (pair : Multiplier → Word → Word → Word × Word)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  Fin.foldl (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes)) (fun a j =>
    let lo := lowerIndex d i lanes j
    let hi := upperIndex d i lanes j
    let u := BF64.Packed.read a lo
    let v := BF64.Packed.read a hi
    let out := pair (p.get i j.divNat) u v
    BF64.Packed.write (BF64.Packed.write a lo out.1) hi out.2) a

/-- One stage, sharing each cached twiddle across all its butterflies. -/
def forwardStage (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  stageSweep p i lanes forwardPair a

/-- One inverse stage, using exactly the forward stage's twiddles. -/
def inverseStage (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  stageSweep p i lanes inversePair a

/-- The lower arithmetic address is the pair partition's lower coordinate. -/
theorem lowerIndex_eq (d : Nat) (i : Fin d) (lanes : Nat)
    (j : Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes))) :
    lowerIndex d i lanes j = stageIndex d i lanes (j, 0) := by
  apply Fin.ext
  change _ = j.val % (2 ^ i.val * lanes) + (2 ^ i.val * lanes) * 0 +
    (2 * (2 ^ i.val * lanes)) * (j.val / (2 ^ i.val * lanes))
  simp only [Nat.mul_zero, Nat.add_zero]
  rfl

/-- The upper arithmetic address is the pair partition's upper coordinate. -/
theorem upperIndex_eq (d : Nat) (i : Fin d) (lanes : Nat)
    (j : Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes))) :
    upperIndex d i lanes j = stageIndex d i lanes (j, 1) := by
  apply Fin.ext
  change j.val % (2 ^ i.val * lanes) +
      (2 * (2 ^ i.val * lanes)) * (j.val / (2 ^ i.val * lanes)) + 2 ^ i.val * lanes =
    j.val % (2 ^ i.val * lanes) + (2 ^ i.val * lanes) * 1 +
      (2 * (2 ^ i.val * lanes)) * (j.val / (2 ^ i.val * lanes))
  omega

/-- The arithmetic sweep refines the disjoint-pair update model. -/
theorem stageSweep_eq_sweep (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (pair : Multiplier → Word → Word → Word × Word)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    stageSweep p i lanes pair a =
      sweep (stageIndex d i lanes) (fun j => pair (p.get i j.divNat)) a := by
  unfold stageSweep sweep
  apply congrArg (fun f : BF64.Packed.Buffer (2 ^ d * lanes) →
    Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes)) →
    BF64.Packed.Buffer (2 ^ d * lanes) => Fin.foldl _ f a)
  funext a j
  simp only [lowerIndex_eq, upperIndex_eq, updatePair]

/-- The forward implementation refines the disjoint-pair model. -/
theorem forwardStage_eq_sweep (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    forwardStage p i lanes a =
      sweep (stageIndex d i lanes) (fun j => forwardPair (p.get i j.divNat)) a :=
  stageSweep_eq_sweep p i lanes forwardPair a

/-- The inverse implementation refines the disjoint-pair model. -/
theorem inverseStage_eq_sweep (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    inverseStage p i lanes a =
      sweep (stageIndex d i lanes) (fun j => inversePair (p.get i j.divNat)) a :=
  stageSweep_eq_sweep p i lanes inversePair a

/-- Encode tiled novel coefficients by running stages `ell-1` through zero. -/
def forward (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  Fin.foldl ell (fun a k => forwardStage p ⟨ell - k.val - 1, by omega⟩ lanes a) a

/-- Recover the tiled novel coefficients by reversing the forward stages. -/
def inverse (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  Fin.foldl ell (fun a k => inverseStage p ⟨k.val, by omega⟩ lanes a) a

/-- Replicate a row-major message into all evaluation cosets. -/
def tileRows (ell rate lanes : Nat) (a : BF64.Packed.Buffer (2 ^ ell * lanes)) :
    BF64.Packed.Buffer (2 ^ (ell + rate) * lanes) :=
  tabulate _ fun j =>
    BF64.Packed.read a ⟨j.val % (2 ^ ell * lanes), by
      have hl : lanes ≠ 0 := by
        intro hz
        have hj := j.isLt
        simp only [hz, Nat.mul_zero, Nat.not_lt_zero] at hj
      have h : 0 < 2 ^ ell * lanes := Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero hl)
      exact Nat.mod_lt _ h⟩

/-- Reverse live lane-major K columns into rows, with absent lanes leading. -/
def tileLanes (ell rate live lanes : Nat) (hlive : live ≤ lanes)
    (a : BF64.Packed.Buffer (live * 2 ^ ell)) :
    BF64.Packed.Buffer (2 ^ (ell + rate) * lanes) :=
  tabulate _ fun j =>
    let lane := j.val % lanes
    if h : lane < lanes - live then ⟨0⟩ else
      let col := lanes - 1 - lane
      let row := j.val / lanes % 2 ^ ell
      BF64.Packed.read a ⟨col * 2 ^ ell + row, by
        have hj : lane < lanes := Nat.mod_lt _ (by
          have hj0 := j.isLt
          by_contra hz
          have : lanes = 0 := by omega
          simp only [this, Nat.mul_zero, Nat.not_lt_zero] at hj0)
        have hc : col < live := by dsimp [col]; omega
        have hr : row < 2 ^ ell := Nat.mod_lt _ (by positivity)
        calc
          col * 2 ^ ell + row < (col + 1) * 2 ^ ell := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
          _ ≤ live * 2 ^ ell := Nat.mul_le_mul_right _ hc⟩

end AdditiveNTT.Packed
