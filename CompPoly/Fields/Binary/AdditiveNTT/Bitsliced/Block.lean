/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Plan

/-! # Scalar-register blocks for lane-parallel binary linear maps -/

@[expose] public section

set_option maxHeartbeats 2000000

namespace AdditiveNTT.Bitsliced

/-- A register block of sixty-four independent binary planes. -/
structure Block where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  w8 : UInt64
  w9 : UInt64
  w10 : UInt64
  w11 : UInt64
  w12 : UInt64
  w13 : UInt64
  w14 : UInt64
  w15 : UInt64
  w16 : UInt64
  w17 : UInt64
  w18 : UInt64
  w19 : UInt64
  w20 : UInt64
  w21 : UInt64
  w22 : UInt64
  w23 : UInt64
  w24 : UInt64
  w25 : UInt64
  w26 : UInt64
  w27 : UInt64
  w28 : UInt64
  w29 : UInt64
  w30 : UInt64
  w31 : UInt64
  w32 : UInt64
  w33 : UInt64
  w34 : UInt64
  w35 : UInt64
  w36 : UInt64
  w37 : UInt64
  w38 : UInt64
  w39 : UInt64
  w40 : UInt64
  w41 : UInt64
  w42 : UInt64
  w43 : UInt64
  w44 : UInt64
  w45 : UInt64
  w46 : UInt64
  w47 : UInt64
  w48 : UInt64
  w49 : UInt64
  w50 : UInt64
  w51 : UInt64
  w52 : UInt64
  w53 : UInt64
  w54 : UInt64
  w55 : UInt64
  w56 : UInt64
  w57 : UInt64
  w58 : UInt64
  w59 : UInt64
  w60 : UInt64
  w61 : UInt64
  w62 : UInt64
  w63 : UInt64

/-- Select a plane by its six-bit index. -/
@[inline] def Block.get (a : Block) (i : Fin 64) : UInt64 :=
  if i.val = 0 then a.w0
  else if i.val = 1 then a.w1
  else if i.val = 2 then a.w2
  else if i.val = 3 then a.w3
  else if i.val = 4 then a.w4
  else if i.val = 5 then a.w5
  else if i.val = 6 then a.w6
  else if i.val = 7 then a.w7
  else if i.val = 8 then a.w8
  else if i.val = 9 then a.w9
  else if i.val = 10 then a.w10
  else if i.val = 11 then a.w11
  else if i.val = 12 then a.w12
  else if i.val = 13 then a.w13
  else if i.val = 14 then a.w14
  else if i.val = 15 then a.w15
  else if i.val = 16 then a.w16
  else if i.val = 17 then a.w17
  else if i.val = 18 then a.w18
  else if i.val = 19 then a.w19
  else if i.val = 20 then a.w20
  else if i.val = 21 then a.w21
  else if i.val = 22 then a.w22
  else if i.val = 23 then a.w23
  else if i.val = 24 then a.w24
  else if i.val = 25 then a.w25
  else if i.val = 26 then a.w26
  else if i.val = 27 then a.w27
  else if i.val = 28 then a.w28
  else if i.val = 29 then a.w29
  else if i.val = 30 then a.w30
  else if i.val = 31 then a.w31
  else if i.val = 32 then a.w32
  else if i.val = 33 then a.w33
  else if i.val = 34 then a.w34
  else if i.val = 35 then a.w35
  else if i.val = 36 then a.w36
  else if i.val = 37 then a.w37
  else if i.val = 38 then a.w38
  else if i.val = 39 then a.w39
  else if i.val = 40 then a.w40
  else if i.val = 41 then a.w41
  else if i.val = 42 then a.w42
  else if i.val = 43 then a.w43
  else if i.val = 44 then a.w44
  else if i.val = 45 then a.w45
  else if i.val = 46 then a.w46
  else if i.val = 47 then a.w47
  else if i.val = 48 then a.w48
  else if i.val = 49 then a.w49
  else if i.val = 50 then a.w50
  else if i.val = 51 then a.w51
  else if i.val = 52 then a.w52
  else if i.val = 53 then a.w53
  else if i.val = 54 then a.w54
  else if i.val = 55 then a.w55
  else if i.val = 56 then a.w56
  else if i.val = 57 then a.w57
  else if i.val = 58 then a.w58
  else if i.val = 59 then a.w59
  else if i.val = 60 then a.w60
  else if i.val = 61 then a.w61
  else if i.val = 62 then a.w62
  else a.w63

/-- Materialize all sixty-four scalar registers. -/
@[inline] def Block.ofFn (f : Fin 64 → UInt64) : Block :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16,
    f 17, f 18, f 19, f 20, f 21, f 22, f 23, f 24, f 25, f 26, f 27, f 28, f 29, f 30, f 31,
    f 32, f 33, f 34, f 35, f 36, f 37, f 38, f 39, f 40, f 41, f 42, f 43, f 44, f 45, f 46,
    f 47, f 48, f 49, f 50, f 51, f 52, f 53, f 54, f 55, f 56, f 57, f 58, f 59, f 60, f 61,
    f 62, f 63⟩

/-- Exchange row-index bit 0 with word-index bit 0. -/
@[inline] def transpose0 (a : Block) : Block :=
  let t0 := ((a.w0 >>> 1) ^^^ a.w1) &&& 6148914691236517205
  let t2 := ((a.w2 >>> 1) ^^^ a.w3) &&& 6148914691236517205
  let t4 := ((a.w4 >>> 1) ^^^ a.w5) &&& 6148914691236517205
  let t6 := ((a.w6 >>> 1) ^^^ a.w7) &&& 6148914691236517205
  let t8 := ((a.w8 >>> 1) ^^^ a.w9) &&& 6148914691236517205
  let t10 := ((a.w10 >>> 1) ^^^ a.w11) &&& 6148914691236517205
  let t12 := ((a.w12 >>> 1) ^^^ a.w13) &&& 6148914691236517205
  let t14 := ((a.w14 >>> 1) ^^^ a.w15) &&& 6148914691236517205
  let t16 := ((a.w16 >>> 1) ^^^ a.w17) &&& 6148914691236517205
  let t18 := ((a.w18 >>> 1) ^^^ a.w19) &&& 6148914691236517205
  let t20 := ((a.w20 >>> 1) ^^^ a.w21) &&& 6148914691236517205
  let t22 := ((a.w22 >>> 1) ^^^ a.w23) &&& 6148914691236517205
  let t24 := ((a.w24 >>> 1) ^^^ a.w25) &&& 6148914691236517205
  let t26 := ((a.w26 >>> 1) ^^^ a.w27) &&& 6148914691236517205
  let t28 := ((a.w28 >>> 1) ^^^ a.w29) &&& 6148914691236517205
  let t30 := ((a.w30 >>> 1) ^^^ a.w31) &&& 6148914691236517205
  let t32 := ((a.w32 >>> 1) ^^^ a.w33) &&& 6148914691236517205
  let t34 := ((a.w34 >>> 1) ^^^ a.w35) &&& 6148914691236517205
  let t36 := ((a.w36 >>> 1) ^^^ a.w37) &&& 6148914691236517205
  let t38 := ((a.w38 >>> 1) ^^^ a.w39) &&& 6148914691236517205
  let t40 := ((a.w40 >>> 1) ^^^ a.w41) &&& 6148914691236517205
  let t42 := ((a.w42 >>> 1) ^^^ a.w43) &&& 6148914691236517205
  let t44 := ((a.w44 >>> 1) ^^^ a.w45) &&& 6148914691236517205
  let t46 := ((a.w46 >>> 1) ^^^ a.w47) &&& 6148914691236517205
  let t48 := ((a.w48 >>> 1) ^^^ a.w49) &&& 6148914691236517205
  let t50 := ((a.w50 >>> 1) ^^^ a.w51) &&& 6148914691236517205
  let t52 := ((a.w52 >>> 1) ^^^ a.w53) &&& 6148914691236517205
  let t54 := ((a.w54 >>> 1) ^^^ a.w55) &&& 6148914691236517205
  let t56 := ((a.w56 >>> 1) ^^^ a.w57) &&& 6148914691236517205
  let t58 := ((a.w58 >>> 1) ^^^ a.w59) &&& 6148914691236517205
  let t60 := ((a.w60 >>> 1) ^^^ a.w61) &&& 6148914691236517205
  let t62 := ((a.w62 >>> 1) ^^^ a.w63) &&& 6148914691236517205
  ⟨a.w0 ^^^ (t0 <<< 1),
    a.w1 ^^^ t0,
    a.w2 ^^^ (t2 <<< 1),
    a.w3 ^^^ t2,
    a.w4 ^^^ (t4 <<< 1),
    a.w5 ^^^ t4,
    a.w6 ^^^ (t6 <<< 1),
    a.w7 ^^^ t6,
    a.w8 ^^^ (t8 <<< 1),
    a.w9 ^^^ t8,
    a.w10 ^^^ (t10 <<< 1),
    a.w11 ^^^ t10,
    a.w12 ^^^ (t12 <<< 1),
    a.w13 ^^^ t12,
    a.w14 ^^^ (t14 <<< 1),
    a.w15 ^^^ t14,
    a.w16 ^^^ (t16 <<< 1),
    a.w17 ^^^ t16,
    a.w18 ^^^ (t18 <<< 1),
    a.w19 ^^^ t18,
    a.w20 ^^^ (t20 <<< 1),
    a.w21 ^^^ t20,
    a.w22 ^^^ (t22 <<< 1),
    a.w23 ^^^ t22,
    a.w24 ^^^ (t24 <<< 1),
    a.w25 ^^^ t24,
    a.w26 ^^^ (t26 <<< 1),
    a.w27 ^^^ t26,
    a.w28 ^^^ (t28 <<< 1),
    a.w29 ^^^ t28,
    a.w30 ^^^ (t30 <<< 1),
    a.w31 ^^^ t30,
    a.w32 ^^^ (t32 <<< 1),
    a.w33 ^^^ t32,
    a.w34 ^^^ (t34 <<< 1),
    a.w35 ^^^ t34,
    a.w36 ^^^ (t36 <<< 1),
    a.w37 ^^^ t36,
    a.w38 ^^^ (t38 <<< 1),
    a.w39 ^^^ t38,
    a.w40 ^^^ (t40 <<< 1),
    a.w41 ^^^ t40,
    a.w42 ^^^ (t42 <<< 1),
    a.w43 ^^^ t42,
    a.w44 ^^^ (t44 <<< 1),
    a.w45 ^^^ t44,
    a.w46 ^^^ (t46 <<< 1),
    a.w47 ^^^ t46,
    a.w48 ^^^ (t48 <<< 1),
    a.w49 ^^^ t48,
    a.w50 ^^^ (t50 <<< 1),
    a.w51 ^^^ t50,
    a.w52 ^^^ (t52 <<< 1),
    a.w53 ^^^ t52,
    a.w54 ^^^ (t54 <<< 1),
    a.w55 ^^^ t54,
    a.w56 ^^^ (t56 <<< 1),
    a.w57 ^^^ t56,
    a.w58 ^^^ (t58 <<< 1),
    a.w59 ^^^ t58,
    a.w60 ^^^ (t60 <<< 1),
    a.w61 ^^^ t60,
    a.w62 ^^^ (t62 <<< 1),
    a.w63 ^^^ t62⟩

/-- Exchange row-index bit 1 with word-index bit 1. -/
@[inline] def transpose1 (a : Block) : Block :=
  let t0 := ((a.w0 >>> 2) ^^^ a.w2) &&& 3689348814741910323
  let t1 := ((a.w1 >>> 2) ^^^ a.w3) &&& 3689348814741910323
  let t4 := ((a.w4 >>> 2) ^^^ a.w6) &&& 3689348814741910323
  let t5 := ((a.w5 >>> 2) ^^^ a.w7) &&& 3689348814741910323
  let t8 := ((a.w8 >>> 2) ^^^ a.w10) &&& 3689348814741910323
  let t9 := ((a.w9 >>> 2) ^^^ a.w11) &&& 3689348814741910323
  let t12 := ((a.w12 >>> 2) ^^^ a.w14) &&& 3689348814741910323
  let t13 := ((a.w13 >>> 2) ^^^ a.w15) &&& 3689348814741910323
  let t16 := ((a.w16 >>> 2) ^^^ a.w18) &&& 3689348814741910323
  let t17 := ((a.w17 >>> 2) ^^^ a.w19) &&& 3689348814741910323
  let t20 := ((a.w20 >>> 2) ^^^ a.w22) &&& 3689348814741910323
  let t21 := ((a.w21 >>> 2) ^^^ a.w23) &&& 3689348814741910323
  let t24 := ((a.w24 >>> 2) ^^^ a.w26) &&& 3689348814741910323
  let t25 := ((a.w25 >>> 2) ^^^ a.w27) &&& 3689348814741910323
  let t28 := ((a.w28 >>> 2) ^^^ a.w30) &&& 3689348814741910323
  let t29 := ((a.w29 >>> 2) ^^^ a.w31) &&& 3689348814741910323
  let t32 := ((a.w32 >>> 2) ^^^ a.w34) &&& 3689348814741910323
  let t33 := ((a.w33 >>> 2) ^^^ a.w35) &&& 3689348814741910323
  let t36 := ((a.w36 >>> 2) ^^^ a.w38) &&& 3689348814741910323
  let t37 := ((a.w37 >>> 2) ^^^ a.w39) &&& 3689348814741910323
  let t40 := ((a.w40 >>> 2) ^^^ a.w42) &&& 3689348814741910323
  let t41 := ((a.w41 >>> 2) ^^^ a.w43) &&& 3689348814741910323
  let t44 := ((a.w44 >>> 2) ^^^ a.w46) &&& 3689348814741910323
  let t45 := ((a.w45 >>> 2) ^^^ a.w47) &&& 3689348814741910323
  let t48 := ((a.w48 >>> 2) ^^^ a.w50) &&& 3689348814741910323
  let t49 := ((a.w49 >>> 2) ^^^ a.w51) &&& 3689348814741910323
  let t52 := ((a.w52 >>> 2) ^^^ a.w54) &&& 3689348814741910323
  let t53 := ((a.w53 >>> 2) ^^^ a.w55) &&& 3689348814741910323
  let t56 := ((a.w56 >>> 2) ^^^ a.w58) &&& 3689348814741910323
  let t57 := ((a.w57 >>> 2) ^^^ a.w59) &&& 3689348814741910323
  let t60 := ((a.w60 >>> 2) ^^^ a.w62) &&& 3689348814741910323
  let t61 := ((a.w61 >>> 2) ^^^ a.w63) &&& 3689348814741910323
  ⟨a.w0 ^^^ (t0 <<< 2),
    a.w1 ^^^ (t1 <<< 2),
    a.w2 ^^^ t0,
    a.w3 ^^^ t1,
    a.w4 ^^^ (t4 <<< 2),
    a.w5 ^^^ (t5 <<< 2),
    a.w6 ^^^ t4,
    a.w7 ^^^ t5,
    a.w8 ^^^ (t8 <<< 2),
    a.w9 ^^^ (t9 <<< 2),
    a.w10 ^^^ t8,
    a.w11 ^^^ t9,
    a.w12 ^^^ (t12 <<< 2),
    a.w13 ^^^ (t13 <<< 2),
    a.w14 ^^^ t12,
    a.w15 ^^^ t13,
    a.w16 ^^^ (t16 <<< 2),
    a.w17 ^^^ (t17 <<< 2),
    a.w18 ^^^ t16,
    a.w19 ^^^ t17,
    a.w20 ^^^ (t20 <<< 2),
    a.w21 ^^^ (t21 <<< 2),
    a.w22 ^^^ t20,
    a.w23 ^^^ t21,
    a.w24 ^^^ (t24 <<< 2),
    a.w25 ^^^ (t25 <<< 2),
    a.w26 ^^^ t24,
    a.w27 ^^^ t25,
    a.w28 ^^^ (t28 <<< 2),
    a.w29 ^^^ (t29 <<< 2),
    a.w30 ^^^ t28,
    a.w31 ^^^ t29,
    a.w32 ^^^ (t32 <<< 2),
    a.w33 ^^^ (t33 <<< 2),
    a.w34 ^^^ t32,
    a.w35 ^^^ t33,
    a.w36 ^^^ (t36 <<< 2),
    a.w37 ^^^ (t37 <<< 2),
    a.w38 ^^^ t36,
    a.w39 ^^^ t37,
    a.w40 ^^^ (t40 <<< 2),
    a.w41 ^^^ (t41 <<< 2),
    a.w42 ^^^ t40,
    a.w43 ^^^ t41,
    a.w44 ^^^ (t44 <<< 2),
    a.w45 ^^^ (t45 <<< 2),
    a.w46 ^^^ t44,
    a.w47 ^^^ t45,
    a.w48 ^^^ (t48 <<< 2),
    a.w49 ^^^ (t49 <<< 2),
    a.w50 ^^^ t48,
    a.w51 ^^^ t49,
    a.w52 ^^^ (t52 <<< 2),
    a.w53 ^^^ (t53 <<< 2),
    a.w54 ^^^ t52,
    a.w55 ^^^ t53,
    a.w56 ^^^ (t56 <<< 2),
    a.w57 ^^^ (t57 <<< 2),
    a.w58 ^^^ t56,
    a.w59 ^^^ t57,
    a.w60 ^^^ (t60 <<< 2),
    a.w61 ^^^ (t61 <<< 2),
    a.w62 ^^^ t60,
    a.w63 ^^^ t61⟩

/-- Exchange row-index bit 2 with word-index bit 2. -/
@[inline] def transpose2 (a : Block) : Block :=
  let t0 := ((a.w0 >>> 4) ^^^ a.w4) &&& 1085102592571150095
  let t1 := ((a.w1 >>> 4) ^^^ a.w5) &&& 1085102592571150095
  let t2 := ((a.w2 >>> 4) ^^^ a.w6) &&& 1085102592571150095
  let t3 := ((a.w3 >>> 4) ^^^ a.w7) &&& 1085102592571150095
  let t8 := ((a.w8 >>> 4) ^^^ a.w12) &&& 1085102592571150095
  let t9 := ((a.w9 >>> 4) ^^^ a.w13) &&& 1085102592571150095
  let t10 := ((a.w10 >>> 4) ^^^ a.w14) &&& 1085102592571150095
  let t11 := ((a.w11 >>> 4) ^^^ a.w15) &&& 1085102592571150095
  let t16 := ((a.w16 >>> 4) ^^^ a.w20) &&& 1085102592571150095
  let t17 := ((a.w17 >>> 4) ^^^ a.w21) &&& 1085102592571150095
  let t18 := ((a.w18 >>> 4) ^^^ a.w22) &&& 1085102592571150095
  let t19 := ((a.w19 >>> 4) ^^^ a.w23) &&& 1085102592571150095
  let t24 := ((a.w24 >>> 4) ^^^ a.w28) &&& 1085102592571150095
  let t25 := ((a.w25 >>> 4) ^^^ a.w29) &&& 1085102592571150095
  let t26 := ((a.w26 >>> 4) ^^^ a.w30) &&& 1085102592571150095
  let t27 := ((a.w27 >>> 4) ^^^ a.w31) &&& 1085102592571150095
  let t32 := ((a.w32 >>> 4) ^^^ a.w36) &&& 1085102592571150095
  let t33 := ((a.w33 >>> 4) ^^^ a.w37) &&& 1085102592571150095
  let t34 := ((a.w34 >>> 4) ^^^ a.w38) &&& 1085102592571150095
  let t35 := ((a.w35 >>> 4) ^^^ a.w39) &&& 1085102592571150095
  let t40 := ((a.w40 >>> 4) ^^^ a.w44) &&& 1085102592571150095
  let t41 := ((a.w41 >>> 4) ^^^ a.w45) &&& 1085102592571150095
  let t42 := ((a.w42 >>> 4) ^^^ a.w46) &&& 1085102592571150095
  let t43 := ((a.w43 >>> 4) ^^^ a.w47) &&& 1085102592571150095
  let t48 := ((a.w48 >>> 4) ^^^ a.w52) &&& 1085102592571150095
  let t49 := ((a.w49 >>> 4) ^^^ a.w53) &&& 1085102592571150095
  let t50 := ((a.w50 >>> 4) ^^^ a.w54) &&& 1085102592571150095
  let t51 := ((a.w51 >>> 4) ^^^ a.w55) &&& 1085102592571150095
  let t56 := ((a.w56 >>> 4) ^^^ a.w60) &&& 1085102592571150095
  let t57 := ((a.w57 >>> 4) ^^^ a.w61) &&& 1085102592571150095
  let t58 := ((a.w58 >>> 4) ^^^ a.w62) &&& 1085102592571150095
  let t59 := ((a.w59 >>> 4) ^^^ a.w63) &&& 1085102592571150095
  ⟨a.w0 ^^^ (t0 <<< 4),
    a.w1 ^^^ (t1 <<< 4),
    a.w2 ^^^ (t2 <<< 4),
    a.w3 ^^^ (t3 <<< 4),
    a.w4 ^^^ t0,
    a.w5 ^^^ t1,
    a.w6 ^^^ t2,
    a.w7 ^^^ t3,
    a.w8 ^^^ (t8 <<< 4),
    a.w9 ^^^ (t9 <<< 4),
    a.w10 ^^^ (t10 <<< 4),
    a.w11 ^^^ (t11 <<< 4),
    a.w12 ^^^ t8,
    a.w13 ^^^ t9,
    a.w14 ^^^ t10,
    a.w15 ^^^ t11,
    a.w16 ^^^ (t16 <<< 4),
    a.w17 ^^^ (t17 <<< 4),
    a.w18 ^^^ (t18 <<< 4),
    a.w19 ^^^ (t19 <<< 4),
    a.w20 ^^^ t16,
    a.w21 ^^^ t17,
    a.w22 ^^^ t18,
    a.w23 ^^^ t19,
    a.w24 ^^^ (t24 <<< 4),
    a.w25 ^^^ (t25 <<< 4),
    a.w26 ^^^ (t26 <<< 4),
    a.w27 ^^^ (t27 <<< 4),
    a.w28 ^^^ t24,
    a.w29 ^^^ t25,
    a.w30 ^^^ t26,
    a.w31 ^^^ t27,
    a.w32 ^^^ (t32 <<< 4),
    a.w33 ^^^ (t33 <<< 4),
    a.w34 ^^^ (t34 <<< 4),
    a.w35 ^^^ (t35 <<< 4),
    a.w36 ^^^ t32,
    a.w37 ^^^ t33,
    a.w38 ^^^ t34,
    a.w39 ^^^ t35,
    a.w40 ^^^ (t40 <<< 4),
    a.w41 ^^^ (t41 <<< 4),
    a.w42 ^^^ (t42 <<< 4),
    a.w43 ^^^ (t43 <<< 4),
    a.w44 ^^^ t40,
    a.w45 ^^^ t41,
    a.w46 ^^^ t42,
    a.w47 ^^^ t43,
    a.w48 ^^^ (t48 <<< 4),
    a.w49 ^^^ (t49 <<< 4),
    a.w50 ^^^ (t50 <<< 4),
    a.w51 ^^^ (t51 <<< 4),
    a.w52 ^^^ t48,
    a.w53 ^^^ t49,
    a.w54 ^^^ t50,
    a.w55 ^^^ t51,
    a.w56 ^^^ (t56 <<< 4),
    a.w57 ^^^ (t57 <<< 4),
    a.w58 ^^^ (t58 <<< 4),
    a.w59 ^^^ (t59 <<< 4),
    a.w60 ^^^ t56,
    a.w61 ^^^ t57,
    a.w62 ^^^ t58,
    a.w63 ^^^ t59⟩

/-- Exchange row-index bit 3 with word-index bit 3. -/
@[inline] def transpose3 (a : Block) : Block :=
  let t0 := ((a.w0 >>> 8) ^^^ a.w8) &&& 71777214294589695
  let t1 := ((a.w1 >>> 8) ^^^ a.w9) &&& 71777214294589695
  let t2 := ((a.w2 >>> 8) ^^^ a.w10) &&& 71777214294589695
  let t3 := ((a.w3 >>> 8) ^^^ a.w11) &&& 71777214294589695
  let t4 := ((a.w4 >>> 8) ^^^ a.w12) &&& 71777214294589695
  let t5 := ((a.w5 >>> 8) ^^^ a.w13) &&& 71777214294589695
  let t6 := ((a.w6 >>> 8) ^^^ a.w14) &&& 71777214294589695
  let t7 := ((a.w7 >>> 8) ^^^ a.w15) &&& 71777214294589695
  let t16 := ((a.w16 >>> 8) ^^^ a.w24) &&& 71777214294589695
  let t17 := ((a.w17 >>> 8) ^^^ a.w25) &&& 71777214294589695
  let t18 := ((a.w18 >>> 8) ^^^ a.w26) &&& 71777214294589695
  let t19 := ((a.w19 >>> 8) ^^^ a.w27) &&& 71777214294589695
  let t20 := ((a.w20 >>> 8) ^^^ a.w28) &&& 71777214294589695
  let t21 := ((a.w21 >>> 8) ^^^ a.w29) &&& 71777214294589695
  let t22 := ((a.w22 >>> 8) ^^^ a.w30) &&& 71777214294589695
  let t23 := ((a.w23 >>> 8) ^^^ a.w31) &&& 71777214294589695
  let t32 := ((a.w32 >>> 8) ^^^ a.w40) &&& 71777214294589695
  let t33 := ((a.w33 >>> 8) ^^^ a.w41) &&& 71777214294589695
  let t34 := ((a.w34 >>> 8) ^^^ a.w42) &&& 71777214294589695
  let t35 := ((a.w35 >>> 8) ^^^ a.w43) &&& 71777214294589695
  let t36 := ((a.w36 >>> 8) ^^^ a.w44) &&& 71777214294589695
  let t37 := ((a.w37 >>> 8) ^^^ a.w45) &&& 71777214294589695
  let t38 := ((a.w38 >>> 8) ^^^ a.w46) &&& 71777214294589695
  let t39 := ((a.w39 >>> 8) ^^^ a.w47) &&& 71777214294589695
  let t48 := ((a.w48 >>> 8) ^^^ a.w56) &&& 71777214294589695
  let t49 := ((a.w49 >>> 8) ^^^ a.w57) &&& 71777214294589695
  let t50 := ((a.w50 >>> 8) ^^^ a.w58) &&& 71777214294589695
  let t51 := ((a.w51 >>> 8) ^^^ a.w59) &&& 71777214294589695
  let t52 := ((a.w52 >>> 8) ^^^ a.w60) &&& 71777214294589695
  let t53 := ((a.w53 >>> 8) ^^^ a.w61) &&& 71777214294589695
  let t54 := ((a.w54 >>> 8) ^^^ a.w62) &&& 71777214294589695
  let t55 := ((a.w55 >>> 8) ^^^ a.w63) &&& 71777214294589695
  ⟨a.w0 ^^^ (t0 <<< 8),
    a.w1 ^^^ (t1 <<< 8),
    a.w2 ^^^ (t2 <<< 8),
    a.w3 ^^^ (t3 <<< 8),
    a.w4 ^^^ (t4 <<< 8),
    a.w5 ^^^ (t5 <<< 8),
    a.w6 ^^^ (t6 <<< 8),
    a.w7 ^^^ (t7 <<< 8),
    a.w8 ^^^ t0,
    a.w9 ^^^ t1,
    a.w10 ^^^ t2,
    a.w11 ^^^ t3,
    a.w12 ^^^ t4,
    a.w13 ^^^ t5,
    a.w14 ^^^ t6,
    a.w15 ^^^ t7,
    a.w16 ^^^ (t16 <<< 8),
    a.w17 ^^^ (t17 <<< 8),
    a.w18 ^^^ (t18 <<< 8),
    a.w19 ^^^ (t19 <<< 8),
    a.w20 ^^^ (t20 <<< 8),
    a.w21 ^^^ (t21 <<< 8),
    a.w22 ^^^ (t22 <<< 8),
    a.w23 ^^^ (t23 <<< 8),
    a.w24 ^^^ t16,
    a.w25 ^^^ t17,
    a.w26 ^^^ t18,
    a.w27 ^^^ t19,
    a.w28 ^^^ t20,
    a.w29 ^^^ t21,
    a.w30 ^^^ t22,
    a.w31 ^^^ t23,
    a.w32 ^^^ (t32 <<< 8),
    a.w33 ^^^ (t33 <<< 8),
    a.w34 ^^^ (t34 <<< 8),
    a.w35 ^^^ (t35 <<< 8),
    a.w36 ^^^ (t36 <<< 8),
    a.w37 ^^^ (t37 <<< 8),
    a.w38 ^^^ (t38 <<< 8),
    a.w39 ^^^ (t39 <<< 8),
    a.w40 ^^^ t32,
    a.w41 ^^^ t33,
    a.w42 ^^^ t34,
    a.w43 ^^^ t35,
    a.w44 ^^^ t36,
    a.w45 ^^^ t37,
    a.w46 ^^^ t38,
    a.w47 ^^^ t39,
    a.w48 ^^^ (t48 <<< 8),
    a.w49 ^^^ (t49 <<< 8),
    a.w50 ^^^ (t50 <<< 8),
    a.w51 ^^^ (t51 <<< 8),
    a.w52 ^^^ (t52 <<< 8),
    a.w53 ^^^ (t53 <<< 8),
    a.w54 ^^^ (t54 <<< 8),
    a.w55 ^^^ (t55 <<< 8),
    a.w56 ^^^ t48,
    a.w57 ^^^ t49,
    a.w58 ^^^ t50,
    a.w59 ^^^ t51,
    a.w60 ^^^ t52,
    a.w61 ^^^ t53,
    a.w62 ^^^ t54,
    a.w63 ^^^ t55⟩

/-- Exchange row-index bit 4 with word-index bit 4. -/
@[inline] def transpose4 (a : Block) : Block :=
  let t0 := ((a.w0 >>> 16) ^^^ a.w16) &&& 281470681808895
  let t1 := ((a.w1 >>> 16) ^^^ a.w17) &&& 281470681808895
  let t2 := ((a.w2 >>> 16) ^^^ a.w18) &&& 281470681808895
  let t3 := ((a.w3 >>> 16) ^^^ a.w19) &&& 281470681808895
  let t4 := ((a.w4 >>> 16) ^^^ a.w20) &&& 281470681808895
  let t5 := ((a.w5 >>> 16) ^^^ a.w21) &&& 281470681808895
  let t6 := ((a.w6 >>> 16) ^^^ a.w22) &&& 281470681808895
  let t7 := ((a.w7 >>> 16) ^^^ a.w23) &&& 281470681808895
  let t8 := ((a.w8 >>> 16) ^^^ a.w24) &&& 281470681808895
  let t9 := ((a.w9 >>> 16) ^^^ a.w25) &&& 281470681808895
  let t10 := ((a.w10 >>> 16) ^^^ a.w26) &&& 281470681808895
  let t11 := ((a.w11 >>> 16) ^^^ a.w27) &&& 281470681808895
  let t12 := ((a.w12 >>> 16) ^^^ a.w28) &&& 281470681808895
  let t13 := ((a.w13 >>> 16) ^^^ a.w29) &&& 281470681808895
  let t14 := ((a.w14 >>> 16) ^^^ a.w30) &&& 281470681808895
  let t15 := ((a.w15 >>> 16) ^^^ a.w31) &&& 281470681808895
  let t32 := ((a.w32 >>> 16) ^^^ a.w48) &&& 281470681808895
  let t33 := ((a.w33 >>> 16) ^^^ a.w49) &&& 281470681808895
  let t34 := ((a.w34 >>> 16) ^^^ a.w50) &&& 281470681808895
  let t35 := ((a.w35 >>> 16) ^^^ a.w51) &&& 281470681808895
  let t36 := ((a.w36 >>> 16) ^^^ a.w52) &&& 281470681808895
  let t37 := ((a.w37 >>> 16) ^^^ a.w53) &&& 281470681808895
  let t38 := ((a.w38 >>> 16) ^^^ a.w54) &&& 281470681808895
  let t39 := ((a.w39 >>> 16) ^^^ a.w55) &&& 281470681808895
  let t40 := ((a.w40 >>> 16) ^^^ a.w56) &&& 281470681808895
  let t41 := ((a.w41 >>> 16) ^^^ a.w57) &&& 281470681808895
  let t42 := ((a.w42 >>> 16) ^^^ a.w58) &&& 281470681808895
  let t43 := ((a.w43 >>> 16) ^^^ a.w59) &&& 281470681808895
  let t44 := ((a.w44 >>> 16) ^^^ a.w60) &&& 281470681808895
  let t45 := ((a.w45 >>> 16) ^^^ a.w61) &&& 281470681808895
  let t46 := ((a.w46 >>> 16) ^^^ a.w62) &&& 281470681808895
  let t47 := ((a.w47 >>> 16) ^^^ a.w63) &&& 281470681808895
  ⟨a.w0 ^^^ (t0 <<< 16),
    a.w1 ^^^ (t1 <<< 16),
    a.w2 ^^^ (t2 <<< 16),
    a.w3 ^^^ (t3 <<< 16),
    a.w4 ^^^ (t4 <<< 16),
    a.w5 ^^^ (t5 <<< 16),
    a.w6 ^^^ (t6 <<< 16),
    a.w7 ^^^ (t7 <<< 16),
    a.w8 ^^^ (t8 <<< 16),
    a.w9 ^^^ (t9 <<< 16),
    a.w10 ^^^ (t10 <<< 16),
    a.w11 ^^^ (t11 <<< 16),
    a.w12 ^^^ (t12 <<< 16),
    a.w13 ^^^ (t13 <<< 16),
    a.w14 ^^^ (t14 <<< 16),
    a.w15 ^^^ (t15 <<< 16),
    a.w16 ^^^ t0,
    a.w17 ^^^ t1,
    a.w18 ^^^ t2,
    a.w19 ^^^ t3,
    a.w20 ^^^ t4,
    a.w21 ^^^ t5,
    a.w22 ^^^ t6,
    a.w23 ^^^ t7,
    a.w24 ^^^ t8,
    a.w25 ^^^ t9,
    a.w26 ^^^ t10,
    a.w27 ^^^ t11,
    a.w28 ^^^ t12,
    a.w29 ^^^ t13,
    a.w30 ^^^ t14,
    a.w31 ^^^ t15,
    a.w32 ^^^ (t32 <<< 16),
    a.w33 ^^^ (t33 <<< 16),
    a.w34 ^^^ (t34 <<< 16),
    a.w35 ^^^ (t35 <<< 16),
    a.w36 ^^^ (t36 <<< 16),
    a.w37 ^^^ (t37 <<< 16),
    a.w38 ^^^ (t38 <<< 16),
    a.w39 ^^^ (t39 <<< 16),
    a.w40 ^^^ (t40 <<< 16),
    a.w41 ^^^ (t41 <<< 16),
    a.w42 ^^^ (t42 <<< 16),
    a.w43 ^^^ (t43 <<< 16),
    a.w44 ^^^ (t44 <<< 16),
    a.w45 ^^^ (t45 <<< 16),
    a.w46 ^^^ (t46 <<< 16),
    a.w47 ^^^ (t47 <<< 16),
    a.w48 ^^^ t32,
    a.w49 ^^^ t33,
    a.w50 ^^^ t34,
    a.w51 ^^^ t35,
    a.w52 ^^^ t36,
    a.w53 ^^^ t37,
    a.w54 ^^^ t38,
    a.w55 ^^^ t39,
    a.w56 ^^^ t40,
    a.w57 ^^^ t41,
    a.w58 ^^^ t42,
    a.w59 ^^^ t43,
    a.w60 ^^^ t44,
    a.w61 ^^^ t45,
    a.w62 ^^^ t46,
    a.w63 ^^^ t47⟩

/-- Exchange row-index bit 5 with word-index bit 5. -/
@[inline] def transpose5 (a : Block) : Block :=
  let t0 := ((a.w0 >>> 32) ^^^ a.w32) &&& 4294967295
  let t1 := ((a.w1 >>> 32) ^^^ a.w33) &&& 4294967295
  let t2 := ((a.w2 >>> 32) ^^^ a.w34) &&& 4294967295
  let t3 := ((a.w3 >>> 32) ^^^ a.w35) &&& 4294967295
  let t4 := ((a.w4 >>> 32) ^^^ a.w36) &&& 4294967295
  let t5 := ((a.w5 >>> 32) ^^^ a.w37) &&& 4294967295
  let t6 := ((a.w6 >>> 32) ^^^ a.w38) &&& 4294967295
  let t7 := ((a.w7 >>> 32) ^^^ a.w39) &&& 4294967295
  let t8 := ((a.w8 >>> 32) ^^^ a.w40) &&& 4294967295
  let t9 := ((a.w9 >>> 32) ^^^ a.w41) &&& 4294967295
  let t10 := ((a.w10 >>> 32) ^^^ a.w42) &&& 4294967295
  let t11 := ((a.w11 >>> 32) ^^^ a.w43) &&& 4294967295
  let t12 := ((a.w12 >>> 32) ^^^ a.w44) &&& 4294967295
  let t13 := ((a.w13 >>> 32) ^^^ a.w45) &&& 4294967295
  let t14 := ((a.w14 >>> 32) ^^^ a.w46) &&& 4294967295
  let t15 := ((a.w15 >>> 32) ^^^ a.w47) &&& 4294967295
  let t16 := ((a.w16 >>> 32) ^^^ a.w48) &&& 4294967295
  let t17 := ((a.w17 >>> 32) ^^^ a.w49) &&& 4294967295
  let t18 := ((a.w18 >>> 32) ^^^ a.w50) &&& 4294967295
  let t19 := ((a.w19 >>> 32) ^^^ a.w51) &&& 4294967295
  let t20 := ((a.w20 >>> 32) ^^^ a.w52) &&& 4294967295
  let t21 := ((a.w21 >>> 32) ^^^ a.w53) &&& 4294967295
  let t22 := ((a.w22 >>> 32) ^^^ a.w54) &&& 4294967295
  let t23 := ((a.w23 >>> 32) ^^^ a.w55) &&& 4294967295
  let t24 := ((a.w24 >>> 32) ^^^ a.w56) &&& 4294967295
  let t25 := ((a.w25 >>> 32) ^^^ a.w57) &&& 4294967295
  let t26 := ((a.w26 >>> 32) ^^^ a.w58) &&& 4294967295
  let t27 := ((a.w27 >>> 32) ^^^ a.w59) &&& 4294967295
  let t28 := ((a.w28 >>> 32) ^^^ a.w60) &&& 4294967295
  let t29 := ((a.w29 >>> 32) ^^^ a.w61) &&& 4294967295
  let t30 := ((a.w30 >>> 32) ^^^ a.w62) &&& 4294967295
  let t31 := ((a.w31 >>> 32) ^^^ a.w63) &&& 4294967295
  ⟨a.w0 ^^^ (t0 <<< 32),
    a.w1 ^^^ (t1 <<< 32),
    a.w2 ^^^ (t2 <<< 32),
    a.w3 ^^^ (t3 <<< 32),
    a.w4 ^^^ (t4 <<< 32),
    a.w5 ^^^ (t5 <<< 32),
    a.w6 ^^^ (t6 <<< 32),
    a.w7 ^^^ (t7 <<< 32),
    a.w8 ^^^ (t8 <<< 32),
    a.w9 ^^^ (t9 <<< 32),
    a.w10 ^^^ (t10 <<< 32),
    a.w11 ^^^ (t11 <<< 32),
    a.w12 ^^^ (t12 <<< 32),
    a.w13 ^^^ (t13 <<< 32),
    a.w14 ^^^ (t14 <<< 32),
    a.w15 ^^^ (t15 <<< 32),
    a.w16 ^^^ (t16 <<< 32),
    a.w17 ^^^ (t17 <<< 32),
    a.w18 ^^^ (t18 <<< 32),
    a.w19 ^^^ (t19 <<< 32),
    a.w20 ^^^ (t20 <<< 32),
    a.w21 ^^^ (t21 <<< 32),
    a.w22 ^^^ (t22 <<< 32),
    a.w23 ^^^ (t23 <<< 32),
    a.w24 ^^^ (t24 <<< 32),
    a.w25 ^^^ (t25 <<< 32),
    a.w26 ^^^ (t26 <<< 32),
    a.w27 ^^^ (t27 <<< 32),
    a.w28 ^^^ (t28 <<< 32),
    a.w29 ^^^ (t29 <<< 32),
    a.w30 ^^^ (t30 <<< 32),
    a.w31 ^^^ (t31 <<< 32),
    a.w32 ^^^ t0,
    a.w33 ^^^ t1,
    a.w34 ^^^ t2,
    a.w35 ^^^ t3,
    a.w36 ^^^ t4,
    a.w37 ^^^ t5,
    a.w38 ^^^ t6,
    a.w39 ^^^ t7,
    a.w40 ^^^ t8,
    a.w41 ^^^ t9,
    a.w42 ^^^ t10,
    a.w43 ^^^ t11,
    a.w44 ^^^ t12,
    a.w45 ^^^ t13,
    a.w46 ^^^ t14,
    a.w47 ^^^ t15,
    a.w48 ^^^ t16,
    a.w49 ^^^ t17,
    a.w50 ^^^ t18,
    a.w51 ^^^ t19,
    a.w52 ^^^ t20,
    a.w53 ^^^ t21,
    a.w54 ^^^ t22,
    a.w55 ^^^ t23,
    a.w56 ^^^ t24,
    a.w57 ^^^ t25,
    a.w58 ^^^ t26,
    a.w59 ^^^ t27,
    a.w60 ^^^ t28,
    a.w61 ^^^ t29,
    a.w62 ^^^ t30,
    a.w63 ^^^ t31⟩

/-- The six exchange passes implement the 64 by 64 bit transpose. -/
@[noinline] def transpose (a : Block) : Block :=
  transpose5 (transpose4 (transpose3 (transpose2 (transpose1 (transpose0 a)))))

/-- Columns of multiplication by one polynomial-coordinate field element. -/
@[inline] def columns (t : UInt64) : Block :=
  let c0 := t
  let c1 := BF64.Word.xtime c0
  let c2 := BF64.Word.xtime c1
  let c3 := BF64.Word.xtime c2
  let c4 := BF64.Word.xtime c3
  let c5 := BF64.Word.xtime c4
  let c6 := BF64.Word.xtime c5
  let c7 := BF64.Word.xtime c6
  let c8 := BF64.Word.xtime c7
  let c9 := BF64.Word.xtime c8
  let c10 := BF64.Word.xtime c9
  let c11 := BF64.Word.xtime c10
  let c12 := BF64.Word.xtime c11
  let c13 := BF64.Word.xtime c12
  let c14 := BF64.Word.xtime c13
  let c15 := BF64.Word.xtime c14
  let c16 := BF64.Word.xtime c15
  let c17 := BF64.Word.xtime c16
  let c18 := BF64.Word.xtime c17
  let c19 := BF64.Word.xtime c18
  let c20 := BF64.Word.xtime c19
  let c21 := BF64.Word.xtime c20
  let c22 := BF64.Word.xtime c21
  let c23 := BF64.Word.xtime c22
  let c24 := BF64.Word.xtime c23
  let c25 := BF64.Word.xtime c24
  let c26 := BF64.Word.xtime c25
  let c27 := BF64.Word.xtime c26
  let c28 := BF64.Word.xtime c27
  let c29 := BF64.Word.xtime c28
  let c30 := BF64.Word.xtime c29
  let c31 := BF64.Word.xtime c30
  let c32 := BF64.Word.xtime c31
  let c33 := BF64.Word.xtime c32
  let c34 := BF64.Word.xtime c33
  let c35 := BF64.Word.xtime c34
  let c36 := BF64.Word.xtime c35
  let c37 := BF64.Word.xtime c36
  let c38 := BF64.Word.xtime c37
  let c39 := BF64.Word.xtime c38
  let c40 := BF64.Word.xtime c39
  let c41 := BF64.Word.xtime c40
  let c42 := BF64.Word.xtime c41
  let c43 := BF64.Word.xtime c42
  let c44 := BF64.Word.xtime c43
  let c45 := BF64.Word.xtime c44
  let c46 := BF64.Word.xtime c45
  let c47 := BF64.Word.xtime c46
  let c48 := BF64.Word.xtime c47
  let c49 := BF64.Word.xtime c48
  let c50 := BF64.Word.xtime c49
  let c51 := BF64.Word.xtime c50
  let c52 := BF64.Word.xtime c51
  let c53 := BF64.Word.xtime c52
  let c54 := BF64.Word.xtime c53
  let c55 := BF64.Word.xtime c54
  let c56 := BF64.Word.xtime c55
  let c57 := BF64.Word.xtime c56
  let c58 := BF64.Word.xtime c57
  let c59 := BF64.Word.xtime c58
  let c60 := BF64.Word.xtime c59
  let c61 := BF64.Word.xtime c60
  let c62 := BF64.Word.xtime c61
  let c63 := BF64.Word.xtime c62
  ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20,
    c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38,
    c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56,
    c57, c58, c59, c60, c61, c62, c63⟩

/-- Row masks of a shared field multiplier. -/
def matrix (t : UInt64) : Block := transpose (columns t)

/-- A compact table of all XOR combinations of four planes. -/
structure Chunk where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  w8 : UInt64
  w9 : UInt64
  w10 : UInt64
  w11 : UInt64
  w12 : UInt64
  w13 : UInt64
  w14 : UInt64
  w15 : UInt64

/-- Four-plane combinations, including the zero combination. -/
@[inline] def Chunk.create (a b c d : UInt64) : Chunk :=
  let t0 : UInt64 := 0
  let t1 := a
  let t2 := b
  let t3 := t2 ^^^ t1
  let t4 := c
  let t5 := t4 ^^^ t1
  let t6 := t4 ^^^ t2
  let t7 := t6 ^^^ t1
  let t8 := d
  let t9 := t8 ^^^ t1
  let t10 := t8 ^^^ t2
  let t11 := t10 ^^^ t1
  let t12 := t8 ^^^ t4
  let t13 := t12 ^^^ t1
  let t14 := t12 ^^^ t2
  let t15 := t14 ^^^ t1
  ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15⟩

/-- Select a chunk entry by the low four bits. -/
@[noinline] def Chunk.get (a : Chunk) (i : UInt64) : UInt64 :=
  if i = 0 then a.w0
  else if i = 1 then a.w1
  else if i = 2 then a.w2
  else if i = 3 then a.w3
  else if i = 4 then a.w4
  else if i = 5 then a.w5
  else if i = 6 then a.w6
  else if i = 7 then a.w7
  else if i = 8 then a.w8
  else if i = 9 then a.w9
  else if i = 10 then a.w10
  else if i = 11 then a.w11
  else if i = 12 then a.w12
  else if i = 13 then a.w13
  else if i = 14 then a.w14
  else a.w15


end AdditiveNTT.Bitsliced
