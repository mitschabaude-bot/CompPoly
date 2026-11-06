/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.MaskedOps
public import CompPoly.Fields.Binary.BF64.MaskedProofs

/-! # Refinement of masked squaring, Frobenius and inversion -/

public section

namespace BF64.Word

/-- Masked squaring agrees with field squaring. -/
@[simp] theorem toField_squareMasked (a : Word) :
    toField (squareMasked a) = toField a * toField a := toField_mulMasked a a

/-- Masked repeated squaring agrees with the specification Frobenius. -/
@[simp] theorem toField_frobeniusMasked (a : Word) (n : Nat) :
    toField (frobeniusMasked a n) = BF64.powTwoPow (toField a) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [frobeniusMasked, BF64.powTwoPow, ih, toField_squareMasked]

private theorem powTwoPow_zero (n : Nat) : BF64.powTwoPow 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [BF64.powTwoPow, mul_zero] using ih

/-- Masked Itoh–Tsujii agrees with field inversion, including zero. -/
@[simp] theorem toField_invMasked (a : Word) : toField (invMasked a) = (toField a)⁻¹ := by
  rw [BF64.inv_def, BF64.invItohTsujii]
  by_cases h : toField a = 0
  · simp only [h, ite_true, invMasked, toField_squareMasked, toField_mulMasked,
      toField_frobeniusMasked, powTwoPow_zero, mul_zero]
  · simp only [h, ite_false, invMasked, toField_squareMasked, toField_mulMasked,
      toField_frobeniusMasked]

end BF64.Word
