/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Scratch
import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Kernel

/-! # Fixed-scalar bit-plane kernel screening and regression checks -/

public section
open AdditiveNTT.Bitsliced BF64

@[noinline] private def chainScratch : Nat → Block → Scratch → Block → Block
  | 0, _, _, a => a
  | n + 1, m, s, a =>
    let s := prepareScratch s a
    chainScratch n m s (applyScratch s m)

private def seed (i : Nat) : UInt64 :=
  0x0123456789abcdef ^^^ ((UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15)

/-- Check transposition and fixed-scalar multiplication or measure a dependent chain. -/
def main (args : List String) : IO Unit := do
  let [mode, rawN] := args | throw <| IO.userError "expected mode count"
  let some n := rawN.toNat? | throw <| IO.userError "invalid count"
  let a := Block.ofFn fun i => seed i.val
  let p := transpose a
  let t := seed 67
  let m := matrix t
  let s : Scratch := ⟨ByteArray.zeros 2048, ByteArray.size_zeros _⟩
  if mode == "check" then
    for i in List.finRange 64 do
      unless (transpose p).get i == a.get i do throw <| IO.userError "transpose inverse"
      for j in List.finRange 64 do
        unless ((p.get i >>> UInt64.ofNat j.val) &&& 1) ==
            ((a.get j >>> UInt64.ofNat i.val) &&& 1) do
          throw <| IO.userError "transpose bit"
      unless (transpose (applyScratch (prepareScratch s p) m)).get i ==
          (Word.mulMasked ⟨t⟩ ⟨a.get i⟩).val do
        throw <| IO.userError "matrix product"
    IO.println "64 transpose coordinates and 4096 bits, 64 scalar products passed"
  else
    let stdout ← IO.getStdout
    let stdin ← IO.getStdin
    stdout.putStrLn "begin 0"
    stdout.flush
    discard <| stdin.getLine
    let start ← IO.monoNanosNow
    let result := chainScratch n m s p
    let stop ← IO.monoNanosNow
    stdout.putStrLn s!"end {stop-start}"
    stdout.flush
    discard <| stdin.getLine
    IO.println s!"sink {result.w0}"
