/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Masked
public import CompPoly.Fields.Binary.BF64.Ext3
public import CompPoly.Fields.Extension.Bytes

/-!
# Three-word arithmetic modulo `Y³ + Y + 1`

The coefficient order is constant, linear, quadratic, matching `BF64.Ext3` and
its 24-byte wire codec. Multiplication uses six base-field products.
-/

@[expose] public section

namespace BF64

/-- Three polynomial-basis words representing the cubic extension. -/
structure WordExt3 where
  /-- Constant coefficient. -/
  c0 : Word
  /-- Linear coefficient. -/
  c1 : Word
  /-- Quadratic coefficient. -/
  c2 : Word
  deriving DecidableEq, BEq, Inhabited, Repr

namespace WordExt3

open CompPoly.Extension

/-- Interpret the three coordinates in the existing extension. -/
def toField (a : WordExt3) : Ext3 :=
  Ext.ofFn fun i => if i.val = 0 then a.c0.toField
    else if i.val = 1 then a.c1.toField else a.c2.toField

/-- Read the three coordinates of the specification carrier. -/
def ofField (a : Ext3) : WordExt3 :=
  ⟨Word.ofField (Ext.coeff a (0 : Fin 3)), Word.ofField (Ext.coeff a (1 : Fin 3)),
    Word.ofField (Ext.coeff a (2 : Fin 3))⟩

@[simp] theorem ofField_toField (a : WordExt3) : ofField (toField a) = a := by
  cases a
  rfl

@[simp] theorem toField_ofField (a : Ext3) : toField (ofField a) = a := by
  apply Ext.ext
  intro i
  fin_cases i <;> rfl

theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

/-- Coefficientwise raw XOR. -/
@[inline] def add (a b : WordExt3) : WordExt3 :=
  ⟨Word.add a.c0 b.c0, Word.add a.c1 b.c1, Word.add a.c2 b.c2⟩

/-- Six-product Karatsuba multiplication, reduced by `Y³ = Y + 1`. -/
@[inline] def mul (a b : WordExt3) : WordExt3 :=
  let p0 := Word.mulMasked a.c0 b.c0
  let p1 := Word.mulMasked a.c1 b.c1
  let p2 := Word.mulMasked a.c2 b.c2
  let p01 := Word.add (Word.add (Word.mulMasked (Word.add a.c0 a.c1) (Word.add b.c0 b.c1)) p0) p1
  let p02 := Word.add (Word.add (Word.mulMasked (Word.add a.c0 a.c2) (Word.add b.c0 b.c2)) p0) p2
  let p12 := Word.add (Word.add (Word.mulMasked (Word.add a.c1 a.c2) (Word.add b.c1 b.c2)) p1) p2
  ⟨Word.add p0 p12, Word.add (Word.add p01 p12) p2,
    Word.add (Word.add p02 p1) p2⟩

/-- Multiply by a base-field scalar using three base-field products. -/
@[inline] def mulScalar (a : WordExt3) (b : Word) : WordExt3 :=
  ⟨Word.mulMasked a.c0 b, Word.mulMasked a.c1 b, Word.mulMasked a.c2 b⟩

/-- Characteristic-two square using three base-field squares. -/
@[inline] def square (a : WordExt3) : WordExt3 :=
  let s2 := Word.mulMasked a.c2 a.c2
  ⟨Word.mulMasked a.c0 a.c0, s2, Word.add (Word.mulMasked a.c1 a.c1) s2⟩

/-- The `2^n` Frobenius, preserving the three-word representation. -/
def frobenius (a : WordExt3) : Nat → WordExt3
  | 0 => a
  | n + 1 => frobenius (square a) n

instance : CompPoly.ByteCodec WordExt3 where
  width := CompPoly.ByteCodec.width Ext3
  toBytes a := CompPoly.ByteCodec.toBytes a.toField
  ofBytes? b := (CompPoly.ByteCodec.ofBytes? b).map ofField
  ofBytes?_toBytes a := by
    simp only [CompPoly.ByteCodec.ofBytes?_toBytes, Option.map_some, ofField_toField]

/-- The codec is exactly the ordered coefficient codec of the specification. -/
@[simp] theorem toBytes_toField (a : WordExt3) :
    CompPoly.ByteCodec.toBytes a = CompPoly.ByteCodec.toBytes a.toField := rfl

end WordExt3
end BF64
