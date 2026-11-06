/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.WordExt3
public import CompPoly.Fields.Binary.BF64.MaskedProofs

/-! # Refinement of the three-word extension kernels -/

@[expose] public section

namespace BF64.WordExt3

open CompPoly.Extension

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] ext3Params

private theorem neg_self (a : BF64) : -a = a := rfl
private theorem two_zero : (2 : BF64) = 0 := rfl
private theorem three_one : (3 : BF64) = 1 := rfl
private theorem four_zero : (4 : BF64) = 0 := rfl

/-- Reduced coefficient 0 of a product in the specification extension. -/
theorem coeff_mul_0 (x y : Ext3) : Ext.coeff (x * y) (0 : Fin 3) =
    Ext.coeff x (0 : Fin 3) * Ext.coeff y (0 : Fin 3) +
      Ext.coeff x (1 : Fin 3) * Ext.coeff y (2 : Fin 3) +
      Ext.coeff x (2 : Fin 3) * Ext.coeff y (1 : Fin 3) := by
  rw [Ext.coeff_mul]
  simp only [Fin.sum_univ_three]
  norm_num [Ext.monomialMod, Function.iterate_succ_apply, Ext.coeff_shiftReduce,
    Ext.coeffNat, ext3Params, ExtensionParams.lowerCoeff, Ext.coeff_one, Ext.coeff_ofFn]
  simp only [neg_self]

/-- Reduced coefficient 1 of a product in the specification extension. -/
theorem coeff_mul_1 (x y : Ext3) : Ext.coeff (x * y) (1 : Fin 3) =
    Ext.coeff x (0 : Fin 3) * Ext.coeff y (1 : Fin 3) +
      Ext.coeff x (1 : Fin 3) * Ext.coeff y (0 : Fin 3) +
      Ext.coeff x (1 : Fin 3) * Ext.coeff y (2 : Fin 3) +
      Ext.coeff x (2 : Fin 3) * Ext.coeff y (1 : Fin 3) +
      Ext.coeff x (2 : Fin 3) * Ext.coeff y (2 : Fin 3) := by
  rw [Ext.coeff_mul]
  simp only [Fin.sum_univ_three]
  norm_num [Ext.monomialMod, Function.iterate_succ_apply, Ext.coeff_shiftReduce,
    Ext.coeffNat, ext3Params, ExtensionParams.lowerCoeff, Ext.coeff_one, Ext.coeff_ofFn]
  simp only [neg_self]; ring

/-- Reduced coefficient 2 of a product in the specification extension. -/
theorem coeff_mul_2 (x y : Ext3) : Ext.coeff (x * y) (2 : Fin 3) =
    Ext.coeff x (0 : Fin 3) * Ext.coeff y (2 : Fin 3) +
      Ext.coeff x (1 : Fin 3) * Ext.coeff y (1 : Fin 3) +
      Ext.coeff x (2 : Fin 3) * Ext.coeff y (0 : Fin 3) +
      Ext.coeff x (2 : Fin 3) * Ext.coeff y (2 : Fin 3) := by
  rw [Ext.coeff_mul]
  simp only [Fin.sum_univ_three]
  norm_num [Ext.monomialMod, Function.iterate_succ_apply, Ext.coeff_shiftReduce,
    Ext.coeffNat, ext3Params, ExtensionParams.lowerCoeff, Ext.coeff_one, Ext.coeff_ofFn]
  simp only [neg_self]; ring

/-- Raw XOR agrees with extension addition. -/
@[simp] theorem toField_add (a b : WordExt3) :
    toField (add a b) = toField a + toField b := by
  apply Ext.ext
  intro i
  fin_cases i <;> simp [toField, add, Ext.coeff_ofFn, Word.toField_add]

/-- Six-product Karatsuba agrees with the quotient extension. -/
@[simp] theorem toField_mul (a b : WordExt3) :
    toField (mul a b) = toField a * toField b := by
  apply Ext.ext
  intro i
  fin_cases i
  · apply Eq.trans ?_ (coeff_mul_0 (toField a) (toField b)).symm
    simp only [mul, toField, Ext.coeff_ofFn, Word.toField_add, Word.toField_mulMasked]
    norm_num
    ring_nf
    simp only [two_zero, mul_zero, add_zero]
  · apply Eq.trans ?_ (coeff_mul_1 (toField a) (toField b)).symm
    simp only [mul, toField, Ext.coeff_ofFn, Word.toField_add, Word.toField_mulMasked]
    norm_num
    ring_nf
    simp only [two_zero, four_zero, mul_zero, add_zero, zero_add]
  · apply Eq.trans ?_ (coeff_mul_2 (toField a) (toField b)).symm
    simp only [mul, toField, Ext.coeff_ofFn, Word.toField_add, Word.toField_mulMasked]
    norm_num
    ring_nf
    simp only [two_zero, mul_zero, add_zero, zero_add]

/-- The mixed product is scalar multiplication through the existing algebra. -/
@[simp] theorem toField_mulScalar (a : WordExt3) (b : Word) :
    toField (mulScalar a b) = b.toField • toField a := by
  apply Ext.ext
  intro i
  fin_cases i <;>
    simp [mulScalar, toField, Ext.coeff_ofFn, Ext.coeff_smul, Word.toField_mulMasked, mul_comm]

/-- Characteristic-two squaring uses three base-field squares. -/
@[simp] theorem toField_square (a : WordExt3) :
    toField (square a) = toField a * toField a := by
  apply Ext.ext
  intro i
  fin_cases i
  · apply Eq.trans ?_ (coeff_mul_0 (toField a) (toField a)).symm
    simp only [square, toField, Ext.coeff_ofFn, Word.toField_add, Word.toField_mulMasked]
    norm_num
    ring_nf
    simp only [two_zero, mul_zero, add_zero]
  · apply Eq.trans ?_ (coeff_mul_1 (toField a) (toField a)).symm
    simp only [square, toField, Ext.coeff_ofFn, Word.toField_add, Word.toField_mulMasked]
    norm_num
    ring_nf
    simp only [two_zero, mul_zero, add_zero]
  · apply Eq.trans ?_ (coeff_mul_2 (toField a) (toField a)).symm
    simp only [square, toField, Ext.coeff_ofFn, Word.toField_add, Word.toField_mulMasked]
    norm_num
    ring_nf
    simp only [two_zero, mul_zero, add_zero]

/-- The extension's word Frobenius agrees with the field power. -/
@[simp] theorem toField_frobenius (a : WordExt3) (n : Nat) :
    toField (frobenius a n) = toField a ^ (2 ^ n) := by
  induction n generalizing a with
  | zero => simp only [frobenius, pow_zero, pow_one]
  | succ n ih =>
    rw [frobenius, ih, toField_square, ← sq, ← pow_mul, pow_succ, Nat.mul_comm]

end BF64.WordExt3
