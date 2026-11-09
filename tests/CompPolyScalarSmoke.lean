/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.AdditiveNTT.Packed.Fused

/-! # Compiled scalar additive-transform stage and prefix regressions -/

public section

open BF64 AdditiveNTT

private def seed (i : Nat) : Word :=
  ⟨0x0123456789abcdef ^^^ ((UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15)⟩

private def check (d lanes : Nat) : IO Unit := do
  if hd : d < 64 then
   if hl : 0 < lanes then
    if hn : 8 * (2 ^ d * lanes) < 4294967296 then
      let p := Bitsliced.Plan.create Packed.flatBasis d hd
      let input := Packed.tabulate (2 ^ d * lanes) fun i => seed i.val
      for hi : i in [:d] do
        let i : Fin d := ⟨i, hi.upper⟩
        let actual := Packed.Scalar.forwardStage p i lanes hl input hn
        let expected := Packed.forwardStage p.toPacked i lanes input
        unless actual.val.bytes == expected.val.bytes do
          throw <| IO.userError s!"scalar stage mismatch: d={d}, lanes={lanes}, i={i.val}"
      for he : ell in [:d + 1] do
        have hell : ell ≤ d := by have h : ell < d + 1 := he.upper; omega
        let actual := Packed.Scalar.forward p ell hell lanes hl input hn
        let expected := Packed.forward p.toPacked ell hell lanes input
        unless actual.val.bytes == expected.val.bytes do
          throw <| IO.userError s!"scalar prefix mismatch: d={d}, lanes={lanes}, ell={ell}"
    else throw <| IO.userError "test buffer exceeds machine bound"
   else throw <| IO.userError "test requires positive lanes"
  else throw <| IO.userError "test domain exceeds field dimension"

/-- Compare complete stored bytes with the certified packed stage and transform. -/
def main : IO Unit := do
  for (d, lanes) in [(0, 1), (1, 3), (4, 1), (5, 8), (6, 48), (7, 56), (8, 64)] do
    check d lanes
  IO.println "Scalar additive stages and all prefixes agree byte-for-byte with packed transforms."
