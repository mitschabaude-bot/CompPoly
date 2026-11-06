/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Transpose
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Butterfly
/-! # Fixed-width encoding of register blocks -/
@[expose] public section
namespace AdditiveNTT.Bitsliced

/-- Register words encode in order as sixty-four little-endian words. -/
instance : CompPoly.ByteCodec Block where
  width := 512
  toBytes a := CompPoly.ByteCodec.toBytes
    (Packed.tabulate 64 fun i => (⟨a.get i⟩ : BF64.Word))
  ofBytes? b := (CompPoly.ByteCodec.ofBytes? (F := BF64.Packed.Buffer 64) b).map fun a =>
    Block.ofFn fun i => (BF64.Packed.read a i).val
  ofBytes?_toBytes a := by
    simp only [CompPoly.ByteCodec.ofBytes?_toBytes, Option.map_some, Option.some.injEq,
      Packed.read_tabulate]
    apply Block.ext
    intro i
    exact Block.get_ofFn _ i

end AdditiveNTT.Bitsliced
