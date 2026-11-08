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

The two halves of the full 64-bit product also have inline PCLMUL/PMULL implementations.
Their Lean bodies remain the masked Karatsuba specification. Compiled field arithmetic uses
these halves for multiplication and reduction; proof checking uses only their Lean bodies.
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

/-- The low word of a 64-by-64 carry-less product. The Lean body is the polynomial spec. -/
@[extern c inline "({
%:if defined(__x86_64__)
  typedef long long clmul_v2di __attribute__((vector_size(16)));
  clmul_v2di p = __builtin_ia32_pclmulqdq128(
    (clmul_v2di){(long long)#1, 0}, (clmul_v2di){(long long)#2, 0}, 0);
  (uint64_t)p[0];
%:elif defined(__aarch64__)
  __uint128_t p = __builtin_neon_vmull_p64(#1, #2);
  (uint64_t)(p >> 0);
%:else
%:error Carry-less multiplication requires x86-64 PCLMUL or AArch64 PMULL
%:endif
})"]
def clMulLo (a b : UInt64) : UInt64 :=
  let lo := clMul32 a b
  let hi := clMul32 (a >>> 32) (b >>> 32)
  let mid := clMul32 (a ^^^ (a >>> 32)) (b ^^^ (b >>> 32)) ^^^ lo ^^^ hi
  lo ^^^ (mid <<< 32)

/-- The high word of a 64-by-64 carry-less product. The Lean body is the polynomial spec. -/
@[extern c inline "({
%:if defined(__x86_64__)
  typedef long long clmul_v2di __attribute__((vector_size(16)));
  clmul_v2di p = __builtin_ia32_pclmulqdq128(
    (clmul_v2di){(long long)#1, 0}, (clmul_v2di){(long long)#2, 0}, 0);
  (uint64_t)p[1];
%:elif defined(__aarch64__)
  __uint128_t p = __builtin_neon_vmull_p64(#1, #2);
  (uint64_t)(p >> 64);
%:else
%:error Carry-less multiplication requires x86-64 PCLMUL or AArch64 PMULL
%:endif
})"]
def clMulHi (a b : UInt64) : UInt64 :=
  let lo := clMul32 a b
  let hi := clMul32 (a >>> 32) (b >>> 32)
  let mid := clMul32 (a ^^^ (a >>> 32)) (b ^^^ (b >>> 32)) ^^^ lo ^^^ hi
  hi ^^^ (mid >>> 32)

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
