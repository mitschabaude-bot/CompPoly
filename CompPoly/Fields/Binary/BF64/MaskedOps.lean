/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Masked

/-! # Squaring, Frobenius and inversion with masked integer products -/

@[expose] public section

namespace BF64.Word

/-- Masked integer squaring; the compiler shares the repeated operand streams. -/
@[inline] def squareMasked (a : Word) : Word := mulMasked a a

/-- The `2^n` Frobenius using masked integer squaring. -/
def frobeniusMasked (a : Word) : Nat → Word
  | 0 => a
  | n + 1 => frobeniusMasked (squareMasked a) n

/-- The degree-64 Itoh–Tsujii chain using masked products, including zero. -/
def invMasked (a : Word) : Word :=
  let u2 := mulMasked (frobeniusMasked a 1) a
  let u3 := mulMasked (frobeniusMasked u2 1) a
  let u6 := mulMasked (frobeniusMasked u3 3) u3
  let u7 := mulMasked (frobeniusMasked u6 1) a
  let u14 := mulMasked (frobeniusMasked u7 7) u7
  let u15 := mulMasked (frobeniusMasked u14 1) a
  let u30 := mulMasked (frobeniusMasked u15 15) u15
  let u31 := mulMasked (frobeniusMasked u30 1) a
  let u62 := mulMasked (frobeniusMasked u31 31) u31
  let u63 := mulMasked (frobeniusMasked u62 1) a
  squareMasked u63

end BF64.Word
