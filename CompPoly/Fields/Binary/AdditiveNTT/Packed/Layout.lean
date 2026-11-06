/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Refinement

/-! # Message tiling and the initial encoder's reversed lane layout -/

@[expose] public section

namespace AdditiveNTT.Packed

open BF64

private theorem interleaved_mod (rows lanes row : Nat) (hrows : 0 < rows)
    (lane : Fin lanes) :
    (lane.val + lanes * row) % (rows * lanes) = lane.val + lanes * (row % rows) := by
  have hr := Nat.mod_lt row hrows
  have hl := lane.isLt
  have hs : lane.val + lanes * (row % rows) < lanes * rows := by nlinarith
  have he : lane.val + lanes * row =
      (lane.val + lanes * (row % rows)) + (lanes * rows) * (row / rows) := by
    calc
      _ = lane.val + lanes * (row % rows + rows * (row / rows)) := by
        rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [Nat.mul_comm rows lanes, he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]

/-- Replication preserves every row-major lane's novel coefficients. -/
theorem laneView_tileRows (ell rate lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ ell * lanes)) (lane : Fin lanes) :
    laneView (tileRows ell rate lanes a) lane = tileCoeffs (R_rate := rate) (laneView a lane) := by
  funext row
  simp only [laneView, tileRows, read_tabulate, tileCoeffs]
  congr 1
  apply Fin.ext
  exact interleaved_mod (2 ^ ell) lanes row.val (by positivity) lane

/-- A padded initial lane is zero in every coset. -/
theorem laneView_tileLanes_zero (ell rate live lanes : Nat) (hlive : live ≤ lanes)
    (a : BF64.Packed.Buffer (live * 2 ^ ell)) (lane : Fin lanes)
    (hpad : lane.val < lanes - live) (row : Fin (2 ^ (ell + rate))) :
    laneView (tileLanes ell rate live lanes hlive a) lane row = ⟨0⟩ := by
  simp only [laneView, tileLanes, read_tabulate]
  have hmod : (finProdFinEquiv (row, lane)).val % lanes = lane.val := by
    change (lane.val + lanes * row.val) % lanes = lane.val
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lane.isLt]
  simp only [hmod, hpad, dite_true]

/-- A live initial lane reads the reversed source column in every coset. -/
theorem laneView_tileLanes_live (ell rate live lanes : Nat) (hlive : live ≤ lanes)
    (a : BF64.Packed.Buffer (live * 2 ^ ell)) (lane : Fin lanes)
    (hlane : lanes - live ≤ lane.val) (row : Fin (2 ^ (ell + rate))) :
    laneView (tileLanes ell rate live lanes hlive a) lane row =
      BF64.Packed.read a ⟨(lanes - 1 - lane.val) * 2 ^ ell + row.val % 2 ^ ell, by
        have hc : lanes - 1 - lane.val < live := by have := lane.isLt; omega
        have hr : row.val % 2 ^ ell < 2 ^ ell := Nat.mod_lt _ (by positivity)
        have _hp : 0 < 2 ^ ell := by positivity
        nlinarith [Nat.mul_le_mul_right (2 ^ ell) hc]⟩ := by
  simp only [laneView, tileLanes, read_tabulate]
  have hmod : (finProdFinEquiv (row, lane)).val % lanes = lane.val := by
    change (lane.val + lanes * row.val) % lanes = lane.val
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lane.isLt]
  have hdiv : (finProdFinEquiv (row, lane)).val / lanes = row.val := by
    change (lane.val + lanes * row.val) / lanes = row.val
    rw [Nat.add_mul_div_left _ _ (by have := lane.isLt; omega),
      Nat.div_eq_of_lt lane.isLt, Nat.zero_add]
  simp only [hmod, show ¬lane.val < lanes - live by omega, dite_false, hdiv]

section Generic

variable {β : Fin 64 → Word} {F : Type} [Field F] [Fintype F]
variable [Fact (Fintype.card F = 2)] [Fact (Nat.Prime (ringChar F))] [Algebra F Word]
variable [Fintype Word] [Fact (LinearIndependent F β)]

/-- Packed row-major encoding agrees with the generic additive encoder in every lane. -/
theorem laneView_encodeRows {ell rate : Nat} (hd : ell + rate < 64)
    (p : Plan β (ell + rate) hd) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ ell * lanes)) (lane : Fin lanes) :
    laneView (forward p ell (by omega) lanes (tileRows ell rate lanes a)) lane =
      computableAdditiveNTT (𝔽q := F) β hd (laneView a lane) := by
  rw [laneView_forward_eq_fold (F := F), laneView_tileRows]
  rfl

end Generic

end AdditiveNTT.Packed
