/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Word

/-!
# Bitsliced BF64 screening workload

Sixty-four independent lanes, including both input transposes and the output
transpose. This benchmark candidate is not part of the certified arithmetic API.
-/

public section

namespace CompPolyBench.BF64Bitslice

/-- Transpose 64 polynomial-coordinate words into 64 bit planes. -/
def pack (a : Array UInt64) : Array UInt64 := Id.run do
  let mut planes := Array.replicate 64 (0 : UInt64)
  for lane in [0:64] do
    for bit in [0:64] do
      planes := planes.set! bit (planes[bit]! ^^^
        (((a[lane]! >>> UInt64.ofNat bit) &&& 1) <<< UInt64.ofNat lane))
  return planes

/-- Transpose 64 bit planes into polynomial-coordinate words. -/
def unpack (a : Array UInt64) : Array UInt64 := pack a

/-- Independent carry-less convolutions and reduction, including packing costs. -/
def mul (a b : Array UInt64) : Array UInt64 := Id.run do
  let a := pack a
  let b := pack b
  let mut c := Array.replicate 128 (0 : UInt64)
  for i in [0:64] do
    for j in [0:64] do
      c := c.set! (i + j) (c[i + j]! ^^^ (a[i]! &&& b[j]!))
  for k in [0:64] do
    let i := 127 - k
    let high := c[i]!
    for offset in [0, 1, 3, 4] do
      let j := i - 64 + offset
      c := c.set! j (c[j]! ^^^ high)
  return unpack (c.extract 0 64)

/-- Dependent sequence of independent 64-lane batches. -/
@[noinline] def chain : Nat → Array UInt64 → Array UInt64 → Array UInt64
  | 0, a, _ => a
  | n + 1, a, b => chain n (mul a b) b

end CompPolyBench.BF64Bitslice
