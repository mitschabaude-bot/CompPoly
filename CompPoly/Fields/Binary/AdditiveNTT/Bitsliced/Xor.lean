/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Block
/-! # Word-parallel addition of bit-plane blocks -/
@[expose] public section
namespace AdditiveNTT.Bitsliced
/-- Coordinatewise binary addition of register blocks. -/
@[inline] def Block.xor (a b : Block) : Block :=
  ⟨a.w0 ^^^ b.w0,
    a.w1 ^^^ b.w1,
    a.w2 ^^^ b.w2,
    a.w3 ^^^ b.w3,
    a.w4 ^^^ b.w4,
    a.w5 ^^^ b.w5,
    a.w6 ^^^ b.w6,
    a.w7 ^^^ b.w7,
    a.w8 ^^^ b.w8,
    a.w9 ^^^ b.w9,
    a.w10 ^^^ b.w10,
    a.w11 ^^^ b.w11,
    a.w12 ^^^ b.w12,
    a.w13 ^^^ b.w13,
    a.w14 ^^^ b.w14,
    a.w15 ^^^ b.w15,
    a.w16 ^^^ b.w16,
    a.w17 ^^^ b.w17,
    a.w18 ^^^ b.w18,
    a.w19 ^^^ b.w19,
    a.w20 ^^^ b.w20,
    a.w21 ^^^ b.w21,
    a.w22 ^^^ b.w22,
    a.w23 ^^^ b.w23,
    a.w24 ^^^ b.w24,
    a.w25 ^^^ b.w25,
    a.w26 ^^^ b.w26,
    a.w27 ^^^ b.w27,
    a.w28 ^^^ b.w28,
    a.w29 ^^^ b.w29,
    a.w30 ^^^ b.w30,
    a.w31 ^^^ b.w31,
    a.w32 ^^^ b.w32,
    a.w33 ^^^ b.w33,
    a.w34 ^^^ b.w34,
    a.w35 ^^^ b.w35,
    a.w36 ^^^ b.w36,
    a.w37 ^^^ b.w37,
    a.w38 ^^^ b.w38,
    a.w39 ^^^ b.w39,
    a.w40 ^^^ b.w40,
    a.w41 ^^^ b.w41,
    a.w42 ^^^ b.w42,
    a.w43 ^^^ b.w43,
    a.w44 ^^^ b.w44,
    a.w45 ^^^ b.w45,
    a.w46 ^^^ b.w46,
    a.w47 ^^^ b.w47,
    a.w48 ^^^ b.w48,
    a.w49 ^^^ b.w49,
    a.w50 ^^^ b.w50,
    a.w51 ^^^ b.w51,
    a.w52 ^^^ b.w52,
    a.w53 ^^^ b.w53,
    a.w54 ^^^ b.w54,
    a.w55 ^^^ b.w55,
    a.w56 ^^^ b.w56,
    a.w57 ^^^ b.w57,
    a.w58 ^^^ b.w58,
    a.w59 ^^^ b.w59,
    a.w60 ^^^ b.w60,
    a.w61 ^^^ b.w61,
    a.w62 ^^^ b.w62,
    a.w63 ^^^ b.w63⟩
/-- Block addition is word XOR in every plane. -/
theorem Block.get_xor (a b : Block) (i : Fin 64) :
    (a.xor b).get i = a.get i ^^^ b.get i := by
  fin_cases i <;> rfl

end AdditiveNTT.Bitsliced
