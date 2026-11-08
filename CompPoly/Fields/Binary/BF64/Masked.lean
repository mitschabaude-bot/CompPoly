/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Word
public import CompPoly.Fields.Binary.BF64.ClMul

/-!
# Masked-integer carry-less products

Four interleaved coefficient streams leave three carry bits between adjacent
coefficients. Ordinary integer products can then be masked and XORed to recover
the carry-less product. Three 32-bit products combine by Karatsuba.

The two halves of the full 64-bit product also have inline PCLMUL/PMULL implementations.
Their Lean bodies remain the masked Karatsuba specification. Compiled field arithmetic uses
these halves for multiplication and reduction; proof checking uses only their Lean bodies.
-/

@[expose] public section

namespace BF64.Word

/-- Reduce a double-width polynomial using the two `0x1b` folds. -/
@[inline] def reduceWide (lo hi : UInt64) : UInt64 :=
  let carry := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  lo ^^^ hi ^^^ (hi <<< 1) ^^^ (hi <<< 3) ^^^ (hi <<< 4) ^^^
    carry ^^^ (carry <<< 1) ^^^ (carry <<< 3) ^^^ (carry <<< 4)

/-- Two carry-less products fold a double-width word modulo the base polynomial. -/
@[inline] def reduceClmul (lo hi : UInt64) : UInt64 :=
  lo ^^^ clMulLo hi 0x1b ^^^ clMulLo (clMulHi hi 0x1b) 0x1b

/-- Base-field reduction is linear in both halves of the polynomial. -/
@[simp] theorem reduceWide_xor (a b c d : UInt64) :
    reduceWide (a ^^^ b) (c ^^^ d) = reduceWide a c ^^^ reduceWide b d := by
  apply UInt64.toBitVec_inj.mp
  simp only [reduceWide, UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', BitVec.ofNat_eq_ofNat, BitVec.toNat_umod,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  simp only [BitVec.shiftLeft_xor_distrib, BitVec.ushiftRight_xor_distrib]
  ac_rfl

/-- Masked-integer base-field multiplication. -/
@[inline] def mulMasked (a b : Word) : Word :=
  let lo := clMul32 a.val b.val
  let hi := clMul32 (a.val >>> 32) (b.val >>> 32)
  let mid := clMul32 (a.val ^^^ (a.val >>> 32)) (b.val ^^^ (b.val >>> 32)) ^^^ lo ^^^ hi
  ⟨reduceWide (lo ^^^ (mid <<< 32)) (hi ^^^ (mid >>> 32))⟩

/-- Hardware carry-less multiplication followed by the two base-field reduction folds. -/
@[inline] def mulClmul (a b : Word) : Word :=
  ⟨reduceClmul (clMulLo a.val b.val) (clMulHi a.val b.val)⟩


end BF64.Word
