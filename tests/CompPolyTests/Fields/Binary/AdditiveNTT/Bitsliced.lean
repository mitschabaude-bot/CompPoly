/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Layout
/-! # Bit-plane transpose, multiplication, encoder and inverse regressions -/
public section
namespace CompPolyTests.Fields.Binary.AdditiveNTT.Bitsliced
open BF64 _root_.AdditiveNTT.Bitsliced

private def seed (i : Nat) : UInt64 :=
  0x0123456789abcdef ^^^ ((UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15)

example (a : Block) : transpose (transpose a) = a := transpose_transpose a

example (a : Block) : CompPoly.ByteCodec.ofBytes? (CompPoly.ByteCodec.toBytes a) = some a :=
  CompPoly.ByteCodec.ofBytes?_toBytes a

/-- Exercise the linked scalar table kernel, transposes, all stage counts and inverse. -/
def runChecks : IO Unit := do
  let a := Block.ofFn fun i => seed i.val
  let planes := transpose a
  let s : Scratch := ⟨ByteArray.zeros 2048, ByteArray.size_zeros _⟩
  for t in [0, 1, 2, 0x8000000000000000, seed 67] do
    let product := applyScratch (prepareScratch s planes) (matrix t)
    for i in List.finRange 64 do
      unless (transpose planes).get i == a.get i do
        throw <| IO.userError "register transpose inverse mismatch"
      unless (transpose product).get i == (Word.mulMasked ⟨t⟩ ⟨a.get i⟩).val do
        throw <| IO.userError "matrix multiplication mismatch"
  for i in List.finRange 64 do
    for j in List.finRange 64 do
      unless ((planes.get i >>> UInt64.ofNat j.val) &&& 1) ==
          ((a.get j >>> UInt64.ofNat i.val) &&& 1) do
        throw <| IO.userError "transpose bit mismatch"
  let p := Plan.create AdditiveNTT.Packed.flatBasis 4 (by decide)
  let input := fromFn 16 (by decide) fun r c => seed (r.val * 64 + c.val)
  let packed := transposeRows input (by decide)
  for ell in [:5] do
    if he : ell ≤ 4 then
      let output := forward p ell he input (by decide)
      let actual := transposeRows output (by decide)
      let expected := AdditiveNTT.Packed.forward p.toPacked ell he 64 packed
      unless actual.val.bytes == expected.val.bytes do
        throw <| IO.userError "packed forward agreement mismatch"
      let recovered := inverse p ell he output (by decide)
      unless recovered.val.bytes == input.val.bytes do
        throw <| IO.userError "bit-plane inverse mismatch"
  IO.println "bit-plane transpose, five scalars, all stage counts and inverse passed"

end CompPolyTests.Fields.Binary.AdditiveNTT.Bitsliced
