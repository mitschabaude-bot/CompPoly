/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public meta import CompPoly.Fields.Binary.BF64.Word
public import CompPoly.Fields.Binary.BF64.Word
public meta import CompPoly.Fields.Binary.BF64.FixedMap
public import CompPoly.Fields.Binary.BF64.FixedMap
public meta import CompPoly.Fields.Binary.BF64.WordExt3
public import CompPoly.Fields.Binary.BF64.WordExt3
public meta import CompPoly.Fields.Binary.BF64.Masked
public import CompPoly.Fields.Binary.BF64.Masked

/-! # Word-kernel differential regressions -/

public meta section

namespace CompPolyTests.Fields.Binary.BF64Word

open BF64

private def check (a b : UInt64) : Bool :=
  (Word.mul ⟨a⟩ ⟨b⟩).toField == Word.toField ⟨a⟩ * Word.toField ⟨b⟩ &&
    Word.mulMasked ⟨a⟩ ⟨b⟩ == Word.mul ⟨a⟩ ⟨b⟩

-- Every monomial pair exercises the reduction boundary and the full word width.
#guard (List.range 64).all fun i => (List.range 64).all fun j =>
  check ((1 : UInt64) <<< UInt64.ofNat i) ((1 : UInt64) <<< UInt64.ofNat j)

private def differential : Bool := Id.run do
  let mut x : UInt64 := 0x0123456789abcdef
  let mut y : UInt64 := 0xfedcba9876543210
  for _ in [0:1024] do
    x := x * 6364136223846793005 + 1442695040888963407
    y := y * 2862933555777941757 + 3037000493
    if !check x y then return false
  return true

#guard differential
#guard check 0 0xffffffffffffffff
#guard check 1 0xffffffffffffffff
#guard (Word.mul ⟨0x8000000000000000⟩ ⟨2⟩).val == 0x1b

private def extChecks : Bool := Id.run do
  let mut x : UInt64 := 0x123456789abcdef
  for _ in [0:32] do
    let a : WordExt3 := ⟨⟨x⟩, ⟨x ^^^ 0xfedcba9876543210⟩, ⟨x + 0x2222222222222222⟩⟩
    x := x * 6364136223846793005 + 1442695040888963407
    let b : WordExt3 := ⟨⟨x⟩, ⟨x ^^^ 0x8000000000000001⟩, ⟨x + 0x1111111111111111⟩⟩
    if (WordExt3.mul a b).toField != a.toField * b.toField then return false
    if (WordExt3.square a).toField != a.toField * a.toField then return false
    if (WordExt3.mulScalar a ⟨x⟩).toField != Word.toField ⟨x⟩ • a.toField then return false
  return true

#guard extChecks

end CompPolyTests.Fields.Binary.BF64Word
