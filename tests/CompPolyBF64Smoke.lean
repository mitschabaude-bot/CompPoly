/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import CompPoly.Fields.Binary.BF64.MaskedOps
import CompPoly.Fields.Binary.BF64.FixedMap
import CompPoly.Fields.Binary.BF64.WordExt3Dot
import CompPoly.Fields.Binary.BF64.WordExt3Frobenius

/-! # Native packed BF64 regressions -/

public section

open BF64 CompPoly

/-- Exercise the native buffer accessors and both prepared-map sizes. -/
def main : IO UInt32 := do
  for scalar in [0, 1, 2, 0xffffffffffffffff, 0xfedcba9876543210] do
    let a : Word := ⟨scalar⟩
    let nibble := Word.NibbleMap.ofScalar a
    let byte := Word.ByteMap.ofScalar a
    let mut x : UInt64 := 0x123456789abcdef
    for _ in [0:128] do
      let b : Word := ⟨x⟩
      unless nibble.mul b == Word.mul a b && byte.mul b == Word.mul a b do
        throw <| IO.userError "fixed-multiplier differential mismatch"
      unless ByteCodec.ofByteArray? (ByteCodec.toByteArray b) == some b do
        throw <| IO.userError "word codec round-trip mismatch"
      x := x * 6364136223846793005 + 1442695040888963407
  for word in [0, 1, 2, 0x8000000000000000, 0xffffffffffffffff, 0x123456789abcdef] do
    let a : Word := ⟨word⟩
    unless Word.squareMasked a == Word.square a &&
        Word.frobeniusMasked a 8 == Word.frobenius a 8 && Word.invMasked a == Word.inv a do
      throw <| IO.userError "masked unary arithmetic mismatch"
  let a := Packed.zeros 17
  let mut a : Packed.Buffer 17 := ⟨a, rfl⟩
  for i in List.finRange 17 do
    a := Packed.write a i ⟨UInt64.ofNat (i.val + 1) * 0xfedcba9876543210⟩
  for i in List.finRange 17 do
    unless (Packed.read a i).val == UInt64.ofNat (i.val + 1) * 0xfedcba9876543210 do
      throw <| IO.userError "packed load/store mismatch"
  let e : WordExt3 := ⟨⟨0x123456789abcdef⟩, ⟨0xfedcba9876543210⟩, ⟨0xffffffffffffffff⟩⟩
  unless WordExt3.frobeniusK e == WordExt3.frobenius e 64 do
    throw <| IO.userError "extension base-field Frobenius mismatch"
  unless ByteCodec.ofByteArray? (ByteCodec.toByteArray e) == some e do
    throw <| IO.userError "extension codec round-trip mismatch"
  unless ((ByteCodec.ofByteArray? (ByteCodec.toByteArray a) : Option (Packed.Buffer 17)).map
      fun a => a.val.bytes) == some a.val.bytes do
    throw <| IO.userError "packed codec round-trip mismatch"
  for n in [0, 1, 7, 64] do
    let f (i : Fin n) : WordExt3 :=
      ⟨⟨UInt64.ofNat i.val ^^^ 0x123456789abcdef⟩,
        ⟨UInt64.ofNat i.val * 0xfedcba9876543210⟩, ⟨0xffffffffffffffff⟩⟩
    let packedA := WordExt3.ofFn n f
    let b := WordExt3.ofFn n fun i => WordExt3.square (f i)
    let mut expected : BF64.Ext3 := 0
    for i in List.finRange n do
      unless WordExt3.read packedA i == f i do
        throw <| IO.userError "extension packed layout mismatch"
      expected := expected + (WordExt3.read packedA i).toField * (WordExt3.read b i).toField
    unless (WordExt3.dot packedA b).toField == expected do
      throw <| IO.userError "extension dot-product mismatch"
  IO.println "BF64 native arithmetic, packed storage, lookup maps and codecs passed"
  pure 0
