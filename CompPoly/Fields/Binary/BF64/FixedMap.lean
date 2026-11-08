/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Packed
public import CompPoly.Fields.Binary.BF64.MaskedProofs

/-!
# Fixed-multiplier lookup maps

A nibble map uses 2 KiB and sixteen lookups per product. A byte map uses 16 KiB
and eight lookups. Construction belongs outside the hot loop; each map owns
its contiguous little-endian table.
-/

@[expose] public section

namespace BF64.Word

/-- A packed 4-bit lookup map for one shared multiplier. -/
structure NibbleMap where
  /-- Position-major products of the scalar by shifted digits. -/
  table : Packed.Buffer 256

namespace NibbleMap

/-- Prepare the lookup map for a shared field scalar. -/
def ofScalar (a : Word) : NibbleMap :=
  ⟨Packed.ofFn 256 fun i => mul a ⟨UInt64.ofNat (i.val % 16) <<<
    UInt64.ofNat (4 * (i.val / 16))⟩⟩

/-- Prepare every table entry with the compiled carry-less field product. -/
def ofScalarClmul (a : Word) : NibbleMap :=
  ⟨Packed.ofFn 256 fun i => mulMasked a ⟨UInt64.ofNat (i.val % 16) <<<
    UInt64.ofNat (4 * (i.val / 16))⟩⟩

/-- Carry-less table construction preserves every stored field coordinate. -/
@[csimp] theorem ofScalar_eq_ofScalarClmul : ofScalar = ofScalarClmul := by
  have hm : BF64.Word.mul = mulMasked := by
    funext a b
    apply toField_injective
    simp only [toField_mul, toField_mulMasked]
  funext a
  simp only [ofScalar, ofScalarClmul, hm]

private theorem digit_lt (a : UInt64) : (a &&& 15).toNat < 16 := by
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)

/-- Multiply using a prepared map, with no table construction in the hot path. -/
@[inline] def mul (m : NibbleMap) (a : Word) : Word :=
  let acc := Packed.read m.table ⟨0 + ((a.val >>> 0) &&& 15).toNat,
      by have := digit_lt (a.val >>> 0); omega⟩
  let acc := add acc (Packed.read m.table ⟨16 + ((a.val >>> 4) &&& 15).toNat,
      by have := digit_lt (a.val >>> 4); omega⟩)
  let acc := add acc (Packed.read m.table ⟨32 + ((a.val >>> 8) &&& 15).toNat,
      by have := digit_lt (a.val >>> 8); omega⟩)
  let acc := add acc (Packed.read m.table ⟨48 + ((a.val >>> 12) &&& 15).toNat,
      by have := digit_lt (a.val >>> 12); omega⟩)
  let acc := add acc (Packed.read m.table ⟨64 + ((a.val >>> 16) &&& 15).toNat,
      by have := digit_lt (a.val >>> 16); omega⟩)
  let acc := add acc (Packed.read m.table ⟨80 + ((a.val >>> 20) &&& 15).toNat,
      by have := digit_lt (a.val >>> 20); omega⟩)
  let acc := add acc (Packed.read m.table ⟨96 + ((a.val >>> 24) &&& 15).toNat,
      by have := digit_lt (a.val >>> 24); omega⟩)
  let acc := add acc (Packed.read m.table ⟨112 + ((a.val >>> 28) &&& 15).toNat,
      by have := digit_lt (a.val >>> 28); omega⟩)
  let acc := add acc (Packed.read m.table ⟨128 + ((a.val >>> 32) &&& 15).toNat,
      by have := digit_lt (a.val >>> 32); omega⟩)
  let acc := add acc (Packed.read m.table ⟨144 + ((a.val >>> 36) &&& 15).toNat,
      by have := digit_lt (a.val >>> 36); omega⟩)
  let acc := add acc (Packed.read m.table ⟨160 + ((a.val >>> 40) &&& 15).toNat,
      by have := digit_lt (a.val >>> 40); omega⟩)
  let acc := add acc (Packed.read m.table ⟨176 + ((a.val >>> 44) &&& 15).toNat,
      by have := digit_lt (a.val >>> 44); omega⟩)
  let acc := add acc (Packed.read m.table ⟨192 + ((a.val >>> 48) &&& 15).toNat,
      by have := digit_lt (a.val >>> 48); omega⟩)
  let acc := add acc (Packed.read m.table ⟨208 + ((a.val >>> 52) &&& 15).toNat,
      by have := digit_lt (a.val >>> 52); omega⟩)
  let acc := add acc (Packed.read m.table ⟨224 + ((a.val >>> 56) &&& 15).toNat,
      by have := digit_lt (a.val >>> 56); omega⟩)
  add acc (Packed.read m.table ⟨240 + ((a.val >>> 60) &&& 15).toNat,
      by have := digit_lt (a.val >>> 60); omega⟩)

end NibbleMap

/-- A packed 8-bit lookup map for one shared multiplier. -/
structure ByteMap where
  /-- Position-major products of the scalar by shifted digits. -/
  table : Packed.Buffer 2048

namespace ByteMap

/-- Prepare the lookup map for a shared field scalar. -/
def ofScalar (a : Word) : ByteMap :=
  ⟨Packed.ofFn 2048 fun i => mul a ⟨UInt64.ofNat (i.val % 256) <<<
    UInt64.ofNat (8 * (i.val / 256))⟩⟩

/-- Prepare every table entry with the compiled carry-less field product. -/
def ofScalarClmul (a : Word) : ByteMap :=
  ⟨Packed.ofFn 2048 fun i => mulMasked a ⟨UInt64.ofNat (i.val % 256) <<<
    UInt64.ofNat (8 * (i.val / 256))⟩⟩

/-- Carry-less table construction preserves every stored field coordinate. -/
@[csimp] theorem ofScalar_eq_ofScalarClmul : ofScalar = ofScalarClmul := by
  have hm : BF64.Word.mul = mulMasked := by
    funext a b
    apply toField_injective
    simp only [toField_mul, toField_mulMasked]
  funext a
  simp only [ofScalar, ofScalarClmul, hm]

private theorem digit_lt (a : UInt64) : (a &&& 255).toNat < 256 := by
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)

/-- Multiply using a prepared map, with no table construction in the hot path. -/
@[inline] def mul (m : ByteMap) (a : Word) : Word :=
  let acc := Packed.read m.table ⟨0 + ((a.val >>> 0) &&& 255).toNat,
      by have := digit_lt (a.val >>> 0); omega⟩
  let acc := add acc (Packed.read m.table ⟨256 + ((a.val >>> 8) &&& 255).toNat,
      by have := digit_lt (a.val >>> 8); omega⟩)
  let acc := add acc (Packed.read m.table ⟨512 + ((a.val >>> 16) &&& 255).toNat,
      by have := digit_lt (a.val >>> 16); omega⟩)
  let acc := add acc (Packed.read m.table ⟨768 + ((a.val >>> 24) &&& 255).toNat,
      by have := digit_lt (a.val >>> 24); omega⟩)
  let acc := add acc (Packed.read m.table ⟨1024 + ((a.val >>> 32) &&& 255).toNat,
      by have := digit_lt (a.val >>> 32); omega⟩)
  let acc := add acc (Packed.read m.table ⟨1280 + ((a.val >>> 40) &&& 255).toNat,
      by have := digit_lt (a.val >>> 40); omega⟩)
  let acc := add acc (Packed.read m.table ⟨1536 + ((a.val >>> 48) &&& 255).toNat,
      by have := digit_lt (a.val >>> 48); omega⟩)
  add acc (Packed.read m.table ⟨1792 + ((a.val >>> 56) &&& 255).toNat,
      by have := digit_lt (a.val >>> 56); omega⟩)

end ByteMap

end BF64.Word
