/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.WordExt3Proofs
import Mathlib.Algebra.CharP.Algebra

/-!
# Base-field Frobenius on the cubic extension

The `2^64` Frobenius fixes the base field and sends `Y` to `Y²`. Its action is
one coordinate XOR because `Y⁴ = Y² + Y`.
-/

public section

namespace BF64.WordExt3

/-- The base-field Frobenius, a coordinate permutation and one XOR. -/
@[expose, inline] def frobeniusK (a : WordExt3) : WordExt3 :=
  ⟨a.c0, a.c2, Word.add a.c1 a.c2⟩

open CompPoly.Extension

set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] ext3Params

local instance : CharP Ext3 2 :=
  charP_of_injective_algebraMap (algebraMap BF64 Ext3).injective 2

private theorem basePow (a : BF64) : a ^ (2 ^ 64) = a := by
  let := Fintype.ofFinite BF64
  simpa only [BF64.card_bf64] using FiniteField.pow_card a

private theorem coeffProduct (x y : Ext3) (i : Fin 3) : Ext.coeff (x * y) i =
    if i.val = 0 then
      Ext.coeff x 0 * Ext.coeff y 0 + Ext.coeff x 1 * Ext.coeff y 2 +
        Ext.coeff x 2 * Ext.coeff y 1
    else if i.val = 1 then
      Ext.coeff x 0 * Ext.coeff y 1 + Ext.coeff x 1 * Ext.coeff y 0 +
        Ext.coeff x 1 * Ext.coeff y 2 + Ext.coeff x 2 * Ext.coeff y 1 +
        Ext.coeff x 2 * Ext.coeff y 2
    else Ext.coeff x 0 * Ext.coeff y 2 + Ext.coeff x 1 * Ext.coeff y 1 +
      Ext.coeff x 2 * Ext.coeff y 0 + Ext.coeff x 2 * Ext.coeff y 2 := by
  fin_cases i
  · exact coeff_mul_0 x y
  · exact coeff_mul_1 x y
  · exact coeff_mul_2 x y

private theorem gen_pow_four : ext3Gen ^ 4 = ext3Gen ^ 2 + ext3Gen := by
  calc ext3Gen ^ 4 = ext3Gen ^ 3 * ext3Gen := by ring
    _ = (ext3Gen + 1) * ext3Gen := by rw [ext3Gen_pow_three]
    _ = ext3Gen ^ 2 + ext3Gen := by ring

private theorem gen_pow_seven : ext3Gen ^ 7 = 1 := by
  calc ext3Gen ^ 7 = (ext3Gen ^ 3) ^ 2 * ext3Gen := by ring
    _ = (ext3Gen + 1) ^ 2 * ext3Gen := by rw [ext3Gen_pow_three]
    _ = (ext3Gen ^ 2 + 1) * ext3Gen := by rw [CharTwo.add_sq, one_pow]
    _ = ext3Gen ^ 3 + ext3Gen := by ring
    _ = 1 := by
      rw [ext3Gen_pow_three, add_comm ext3Gen 1, add_assoc,
        CharTwo.add_self_eq_zero, add_zero]

private theorem gen_pow_card : ext3Gen ^ (2 ^ 64) = ext3Gen ^ 2 := by
  calc ext3Gen ^ (2 ^ 64) = ext3Gen ^ (2 ^ 64 % 7 + 7 * (2 ^ 64 / 7)) := by
        rw [Nat.mod_add_div]
    _ = ext3Gen ^ (2 ^ 64 % 7) * (ext3Gen ^ 7) ^ (2 ^ 64 / 7) := by
      rw [pow_add, pow_mul]
    _ = ext3Gen ^ 2 := by
      rw [gen_pow_seven, one_pow, mul_one]
      exact congrArg (fun n : Nat => ext3Gen ^ n) (by decide)

private theorem gen_sq_pow_card : (ext3Gen ^ 2) ^ (2 ^ 64) =
    ext3Gen ^ 2 + ext3Gen := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, gen_pow_card, ← pow_mul]
  exact gen_pow_four

private theorem decompose (a : WordExt3) :
    a.toField = algebraMap BF64 Ext3 a.c0.toField +
      algebraMap BF64 Ext3 a.c1.toField * ext3Gen +
      algebraMap BF64 Ext3 a.c2.toField * ext3Gen ^ 2 := by
  apply Ext.ext
  intro i
  fin_cases i <;>
    simp only [pow_two, coeffProduct, Ext.coeff_add, Ext.algebraMap_eq_ofBase,
      Ext.coeff_ofBase, ext3Gen, Ext.coeff_gen, toField, Ext.coeff_ofFn] <;> norm_num

/-- The coordinate formula agrees with the extension's `2^64` power. -/
@[simp] theorem toField_frobeniusK (a : WordExt3) :
    toField (frobeniusK a) = toField a ^ (2 ^ 64) := by
  change toField ⟨a.c0, a.c2, Word.add a.c1 a.c2⟩ = _
  rw [decompose, decompose a]
  simp only [add_pow_char_pow, mul_pow, ← map_pow, basePow, gen_pow_card,
    gen_sq_pow_card, Word.toField_add, map_add]
  ring

end BF64.WordExt3
