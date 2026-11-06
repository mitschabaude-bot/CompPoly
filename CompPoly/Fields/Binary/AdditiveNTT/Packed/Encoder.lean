/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Extension

/-!
# Packed additive encoder interfaces

Messages contain normalized novel-basis coefficients. Row encoding preserves
lane order; initial encoding reverses lane-major columns and puts padding first.
Inverse decoding returns novel coefficients, with no monomial conversion.
-/

@[expose] public section

namespace AdditiveNTT.Packed

open BF64

/-- Encode row-major K lanes, or three consecutive K limbs per E lane. -/
def encodeRows {ell rate : Nat} {hd : ell + rate < 64} (p : FlatPlan (ell + rate) hd) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ ell * lanes)) :
    BF64.Packed.Buffer (2 ^ (ell + rate) * lanes) :=
  forward p ell (by omega) lanes (tileRows ell rate lanes a)

/-- Encode initial lane-major columns in the reversed, leading-zero-padded layout. -/
def encodeInitial {ell rate : Nat} {hd : ell + rate < 64} (p : FlatPlan (ell + rate) hd)
    (live lanes : Nat) (hlive : live ≤ lanes) (a : BF64.Packed.Buffer (live * 2 ^ ell)) :
    BF64.Packed.Buffer (2 ^ (ell + rate) * lanes) :=
  forward p ell (by omega) lanes (tileLanes ell rate live lanes hlive a)

/-- Invert the codeword and retain the first coset of row-major novel coefficients. -/
def decodeRows {ell rate : Nat} {hd : ell + rate < 64} (p : FlatPlan (ell + rate) hd) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ (ell + rate) * lanes)) :
    BF64.Packed.Buffer (2 ^ ell * lanes) :=
  let recovered := inverse p ell (by omega) lanes a
  tabulate _ fun j => BF64.Packed.read recovered ⟨j.val, by
    have h : 2 ^ ell ≤ 2 ^ (ell + rate) := Nat.pow_le_pow_right (by omega) (by omega)
    exact lt_of_lt_of_le j.isLt (Nat.mul_le_mul_right lanes h)⟩

/-- Decode a valid row-major encoding, recovering every message word. -/
theorem read_decodeRows_encodeRows {ell rate : Nat} {hd : ell + rate < 64}
    (p : FlatPlan (ell + rate) hd)
    (lanes : Nat) (a : BF64.Packed.Buffer (2 ^ ell * lanes)) (j : Fin (2 ^ ell * lanes)) :
    BF64.Packed.read (decodeRows p lanes (encodeRows p lanes a)) j =
      BF64.Packed.read a j := by
  simp only [decodeRows, encodeRows, read_tabulate, read_inverse_forward, tileRows]
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt j.isLt

/-- Initial encoding agrees with the generic encoder on the explicitly permuted message. -/
theorem laneView_encodeInitial {ell rate : Nat} (hd : ell + rate < 64)
    (p : FlatPlan (ell + rate) hd) (live lanes : Nat) (hlive : live ≤ lanes)
    (a : BF64.Packed.Buffer (live * 2 ^ ell)) (lane : Fin lanes) :
    laneView (encodeInitial p live lanes hlive a) lane =
      computableAdditiveNTT (𝔽q := ZMod 2) flatBasis hd
        (laneView (tileLanes ell 0 live lanes hlive a) lane) := by
  classical
  let : Fintype Word := Fintype.ofFinite Word
  rw [encodeInitial, laneView_forward_eq_fold (F := ZMod 2)]
  change _ = Fin.foldl ell _ _
  congr 1
  funext row
  by_cases h : lane.val < lanes - live
  · rw [laneView_tileLanes_zero _ _ _ _ _ _ _ h]
    simp only [tileCoeffs, laneView_tileLanes_zero _ _ _ _ _ _ _ h]
  · have hn : lanes - live ≤ lane.val := by omega
    rw [laneView_tileLanes_live _ _ _ _ _ _ _ hn]
    simp only [tileCoeffs, laneView_tileLanes_live _ _ _ _ _ _ _ hn, Nat.mod_mod]

end AdditiveNTT.Packed
