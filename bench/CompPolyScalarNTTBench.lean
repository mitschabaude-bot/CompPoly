/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.AdditiveNTT.Packed.Scalar

/-! # Matched scalar additive encoder and stage-conformance runner -/

public section

open BF64 AdditiveNTT.Packed

private def seed (i : Nat) : Word :=
  ⟨0x0123456789abcdef ^^^ ((UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15)⟩

private def digest (a : BF64.Packed.Buffer n) : UInt64 × UInt64 :=
  Fin.foldl n (fun (acc : UInt64 × UInt64) i =>
    let x := (BF64.Packed.read a i).val
    ((acc.1 ^^^ x) * 0x100000001b3,
      ((acc.2 <<< 7) ||| (acc.2 >>> 57)) + x)) (0xcbf29ce484222325, 0x84222325cbf29ce4)

private def report (label : String) (a : BF64.Packed.Buffer n) : IO Unit := do
  let (lo, hi) := digest a
  IO.println s!"{label} {n} {lo} {hi}"

@[noinline] private def encode (p : AdditiveNTT.Bitsliced.Plan flatBasis d hd) (ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (hl : 0 < lanes) (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (input : Unit → BF64.Packed.Buffer (2 ^ d * lanes)) :=
  Scalar.forward p ell hell lanes hl (input ()) hn

/-- Run a matched encoding workload, a stage digest fixture, or an exact-byte dump. -/
def main (args : List String) : IO UInt32 := do
  let mode :: layout :: rawD :: rawLive :: rawRate :: rest := args
    | throw <| IO.userError "expected mode layout log-domain live-lanes log-rate [dump-path]"
  let some d := rawD.toNat? | throw <| IO.userError "invalid domain"
  let some live := rawLive.toNat? | throw <| IO.userError "invalid lanes"
  let some rate := rawRate.toNat? | throw <| IO.userError "invalid rate"
  unless layout == "k" || layout == "e" do throw <| IO.userError "layout must be k or e"
  unless live > 0 do throw <| IO.userError "positive lane count required"
  unless mode == "bench" || mode == "check" || mode == "dump" do
    throw <| IO.userError "mode must be bench, check or dump"
  if hd : d < 64 then
    if hr : rate ≤ d then
      let lanes := if layout == "k" then (live + 7) / 8 * 8 else 3 * live
      if hl : 0 < lanes then
       if hn : 8 * (2 ^ d * lanes) < 4294967296 then
        let ell := d - rate
        have hell : ell ≤ d := by omega
        let setupStart ← IO.monoNanosNow
        let p := AdditiveNTT.Bitsliced.Plan.create flatBasis d hd
        let setupStop ← IO.monoNanosNow
        let stdout ← IO.getStdout
        let stdin ← IO.getStdin
        have he : ell + rate = d := by omega
        let makeInput : Unit → BF64.Packed.Buffer (2 ^ d * lanes) ← if layout == "k" then do
            let a := tabulate (live * 2 ^ ell) fun i => seed i.val
            let (lo, hi) := digest a
            IO.eprintln s!"message {lo}:{hi}"
            pure <| fun _ => he ▸ Scalar.tileLanes ell rate live lanes hl (by
              simp only [lanes]
              split
              · omega
              · omega) a (by simpa only [he] using hn)
          else do
            let a := tabulate (2 ^ ell * lanes) fun i => seed i.val
            let (lo, hi) := digest a
            IO.eprintln s!"message {lo}:{hi}"
            pure <| fun _ => he ▸ Scalar.tileRows ell rate lanes hl a (by simpa only [he] using hn)
        if mode == "bench" then
          stdout.putStrLn s!"begin {setupStop - setupStart}"
          stdout.flush
          discard <| stdin.getLine
          let start ← IO.monoNanosNow
          let output := encode p ell hell lanes hl hn makeInput
          let stop ← IO.monoNanosNow
          stdout.putStrLn s!"end {stop - start}"
          stdout.flush
          discard <| stdin.getLine
          let (lo, hi) := digest output
          stdout.putStrLn s!"sink {lo}:{hi}"
          stdout.flush
        else
          let input := makeInput ()
          report "input" input
          let mut output := input
          for hk : k in [:ell] do
            have hklt : k < ell := hk.upper
            let i : Fin d := ⟨ell - k - 1, by omega⟩
            output := Scalar.forwardStage p i lanes hl output hn
            report s!"stage-{i.val}" output
          report "output" output
          let recovered := inverse p.toPacked ell hell lanes output
          unless recovered.val.bytes == input.val.bytes do
            throw <| IO.userError "inverse did not recover tiled input"
          if mode == "dump" then
            let [path] := rest | throw <| IO.userError "dump requires one output path"
            IO.FS.writeBinFile path output.val.bytes
        pure 0
       else throw <| IO.userError "codeword exceeds machine bound"
      else throw <| IO.userError "positive lane count required"
    else throw <| IO.userError "rate exceeds domain"
  else throw <| IO.userError "domain must be below 64"
