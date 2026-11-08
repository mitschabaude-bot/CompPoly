/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

/-! # Native carry-less multiplication with a pure Lean specification -/

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

end BF64.Word
