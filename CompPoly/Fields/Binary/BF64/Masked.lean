/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Word

/-!
# Masked-integer carry-less products

Four interleaved coefficient streams leave three carry bits between adjacent
coefficients. Ordinary integer products can then be masked and XORed to recover
the carry-less product. Three 32-bit products combine by Karatsuba.
-/

@[expose] public section

namespace BF64.Word

/-- Full carry-less product of the low 32 bits of two words, using integer multipliers. -/
@[inline] def clMul32 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0x11111111
  let a1 := a &&& 0x22222222
  let a2 := a &&& 0x44444444
  let a3 := a &&& 0x88888888
  let b0 := b &&& 0x11111111
  let b1 := b &&& 0x22222222
  let b2 := b &&& 0x44444444
  let b3 := b &&& 0x88888888
  let c0 := ((a0 * b0) ^^^ (a1 * b3) ^^^ (a2 * b2) ^^^ (a3 * b1)) &&& 0x1111111111111111
  let c1 := ((a0 * b1) ^^^ (a1 * b0) ^^^ (a2 * b3) ^^^ (a3 * b2)) &&& 0x2222222222222222
  let c2 := ((a0 * b2) ^^^ (a1 * b1) ^^^ (a2 * b0) ^^^ (a3 * b3)) &&& 0x4444444444444444
  let c3 := ((a0 * b3) ^^^ (a1 * b2) ^^^ (a2 * b1) ^^^ (a3 * b0)) &&& 0x8888888888888888
  c0 ^^^ c1 ^^^ c2 ^^^ c3

/-- Reduce a double-width polynomial using the two `0x1b` folds. -/
@[inline] def reduceWide (lo hi : UInt64) : UInt64 :=
  let carry := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  lo ^^^ hi ^^^ (hi <<< 1) ^^^ (hi <<< 3) ^^^ (hi <<< 4) ^^^
    carry ^^^ (carry <<< 1) ^^^ (carry <<< 3) ^^^ (carry <<< 4)

/-- Masked-integer base-field multiplication. -/
@[inline] def mulMasked (a b : Word) : Word :=
  let lo := clMul32 a.val b.val
  let hi := clMul32 (a.val >>> 32) (b.val >>> 32)
  let mid := clMul32 (a.val ^^^ (a.val >>> 32)) (b.val ^^^ (b.val >>> 32)) ^^^ lo ^^^ hi
  ⟨reduceWide (lo ^^^ (mid <<< 32)) (hi ^^^ (mid >>> 32))⟩

end BF64.Word
