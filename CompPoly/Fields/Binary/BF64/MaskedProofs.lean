/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.MaskedProducts

/-! # Refinement of masked-integer BF64 multiplication -/

public section

namespace BF64.Word
open BinaryField Polynomial MaskedLemmas
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Masked-integer multiplication refines the existing BF64 quotient field. -/
@[simp] theorem toField_mulMasked (a b : Word) :
    toField (mulMasked a b) = toField a * toField b := by
  apply BF64.ext
  change (reduceWide _ _).toBitVec = reduce (carryLessMul (w := 128) a.val.toBitVec b.val.toBitVec)
  rw [reduceWide_eq]
  apply congrArg reduce
  have hp : ∀ {w : Nat} (x y : BitVec w), toPoly x = toPoly y → x = y := by
    intro w x y h
    have hz : toPoly (x ^^^ y) = 0 := by rw [toPoly_xor, h, ZMod2Poly.add_self_cancel]
    have hx : x ^^^ y = 0 := by
      by_contra hn
      exact (toPoly_ne_zero_iff_ne_zero _).mpr hn hz
    exact BitVec.xor_eq_zero_iff.mp hx
  apply hp
  let lo := clMul32 a.val b.val
  let hi := clMul32 (a.val >>> 32) (b.val >>> 32)
  let mid := clMul32 (a.val ^^^ (a.val >>> 32)) (b.val ^^^ (b.val >>> 32)) ^^^ lo ^^^ hi
  change toPoly ((lo.toBitVec ^^^ (mid.toBitVec <<< (32 : Nat))).setWidth 128 ^^^
    ((hi.toBitVec ^^^ (mid.toBitVec >>> (32 : Nat))).setWidth 128 <<< (64 : Nat))) = _
  rw [widePoly]
  dsimp only [lo, hi, mid]
  simp only [toPoly_xor, clMul32_poly, UInt64.toBitVec_xor,
    UInt64.toBitVec_shiftRight, BitVec.setWidth_xor, toPoly_xor]
  rw [toPoly_carryLessMul _ _ (by omega), splitPoly32 a.val.toBitVec,
    splitPoly32 b.val.toBitVec]
  simp only [UInt64.toBitVec_ofNat, BitVec.ushiftRight_eq', BitVec.toNat_umod,
    BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  ring_nf
  simp only [ZMod2Poly.two_eq_zero, mul_zero, add_zero]

end BF64.Word
