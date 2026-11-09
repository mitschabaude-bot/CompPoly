/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.AdditiveNTT.Packed.Gathered

/-! # Compiled scalar additive-transform stage and prefix regressions -/

public section

set_option maxRecDepth 4096

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
      for hi : i in [:d - 1] do
        have hir : i + 1 < d := by have h : i < d - 1 := hi.upper; omega
        for chunk in [0, i / 2, i] do
          if hc : chunk ≤ i then
            let gathered := Packed.Gathered.quad (fun i g => p.get i g)
              i chunk lanes hir hc hl input hn
            let serial := Packed.Scalar.forwardQuadNative p i lanes hir hl input hn
            unless gathered.val.bytes == serial.val.bytes do
              throw <| IO.userError
                s!"gathered mismatch: d={d}, lanes={lanes}, i={i}, chunk={chunk}"
      for he : ell in [:d + 1] do
        have hell : ell ≤ d := by have h : ell < d + 1 := he.upper; omega
        let actual := Packed.Scalar.forward p ell hell lanes hl input hn
        let expected := Packed.forward p.toPacked ell hell lanes input
        let near := Packed.Window.nearDepth 8 d ell lanes
        have hnear : near ≤ d := le_trans (Packed.Window.nearDepth_le ..) hell
        let windows := Packed.Window.run 8 (fun i g => p.get i g) ell lanes hell hl input hn
          (fun _ out => out.val.bytes.size)
        for hb : b in [:2 ^ (d - near)] do
          let block : Fin (2 ^ (d - near)) := ⟨b, hb.upper⟩
          let expectedWindow := Packed.Window.extract expected near hnear block
          unless windows[b].1.val.bytes == expectedWindow.val.bytes &&
              windows[b].2 == expectedWindow.val.bytes.size do
            throw <| IO.userError s!"deep window/sink mismatch: d={d}, ell={ell}, block={b}"
        let window := Packed.Window.forward (fun i g => p.get i g) ell hell lanes hl input hn
        unless window.val.bytes == expected.val.bytes do
          throw <| IO.userError s!"window prefix mismatch: d={d}, lanes={lanes}, ell={ell}"
        unless actual.val.bytes == expected.val.bytes do
          throw <| IO.userError s!"scalar prefix mismatch: d={d}, lanes={lanes}, ell={ell}"
    else throw <| IO.userError "test buffer exceeds machine bound"
   else throw <| IO.userError "test requires positive lanes"
  else throw <| IO.userError "test domain exceeds field dimension"

private def checkSchedule (d ell : Nat) : IO Unit := do
  if hd : d < 64 then
    if h : ell ≤ d then
      if hn : 8 * (2 ^ d * 1) < 4294967296 then
        let plan := Bitsliced.Plan.create Packed.flatBasis d hd
        let input := Packed.tabulate (2 ^ d * 1) fun i => seed i.val
        let expected := Packed.Scalar.forward plan ell h 1 (by decide) input hn
        for workers in [1, 2, 4, 8] do
          let actual := Packed.Gathered.forward workers plan ell h 1 (by decide) input hn
          unless actual.val.bytes == expected.val.bytes do
            throw <| IO.userError s!"parallel schedule mismatch: ell={ell}, workers={workers}"

/-- Compare complete stored bytes with the certified packed stage and transform. -/
def main : IO Unit := do
  for (d, lanes) in [(0, 1), (1, 3), (4, 1), (5, 8), (6, 48), (7, 56), (8, 64)] do
    check d lanes
  checkSchedule 12 3
  checkSchedule 12 12
  IO.println "Scalar additive stages and all prefixes agree byte-for-byte with packed transforms."
