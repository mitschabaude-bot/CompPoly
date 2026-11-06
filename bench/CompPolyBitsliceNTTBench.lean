/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Layout
/-! # Matched bit-plane encoder and Rust conformance runner -/
public section
open BF64 AdditiveNTT.Bitsliced AdditiveNTT.Packed

private def seed (i : Nat) : Word :=
  ⟨0x0123456789abcdef ^^^ ((UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15)⟩

private def digest (a : Rows rows) (lanes : Nat) (hlanes : lanes ≤ 64) : UInt64 × UInt64 :=
  Fin.foldl (rows * lanes) (fun (acc : UInt64 × UInt64) i =>
    let off := i.val % lanes + 64 * (i.val / lanes)
    have hi : off < rows * 64 := by
      have hl : 0 < lanes := by by_contra h; have := i.isLt; simp_all
      have hr : i.val / lanes < rows := (Nat.div_lt_iff_lt_mul hl).mpr i.isLt
      have hc := Nat.mod_lt i.val hl
      dsimp [off]
      omega
    let x := (BF64.Packed.read a ⟨off, hi⟩).val
    ((acc.1 ^^^ x) * 0x100000001b3,
      ((acc.2 <<< 7) ||| (acc.2 >>> 57)) + x)) (0xcbf29ce484222325, 0x84222325cbf29ce4)

private def report (label : String) (a : Rows rows) (hn : 8 * (rows * 64) < 4294967296)
    (lanes : Nat) (hlanes : lanes ≤ 64) : IO Unit := do
  let (lo, hi) := digest (transposeRows a hn) lanes hlanes
  IO.println s!"{label} {rows * lanes} {lo} {hi}"

@[noinline] private def encode (p : AdditiveNTT.Bitsliced.Plan flatBasis d hd)
    (ell : Nat) (hell : ell ≤ d)
    (hn : 8 * (2 ^ d * 64) < 4294967296) (input : Unit → Rows (2 ^ d)) :=
  transposeRows (AdditiveNTT.Bitsliced.forward p ell hell (input ()) hn) hn

@[noinline] private def buildInput (layout : String) (rows messageRows live lanes : Nat)
    (hn : 8 * (rows * 64) < 4294967296) (input : BF64.Packed)
    (hInput : input.size = if layout == "k" then live * messageRows else messageRows * lanes)
    (hrows : 0 < messageRows) : Rows rows :=
  fromFn rows hn fun row lane =>
    if h : lane.val < lanes then
      if hLayout : layout == "k" then
        if hh : lane.val < lanes - live then 0 else
          let col := lanes - 1 - lane.val
          let off := col * messageRows + row.val % messageRows
          have hoff : off < live * messageRows := by
            have hc : col < live := by dsimp [col]; omega
            have hb := Nat.mod_lt row.val hrows
            dsimp [off]
            have hp := hrows
            nlinarith
          (input.get ⟨off, by rw [hInput]; simpa only [hLayout, ite_true] using hoff⟩).val
      else
        let off := row.val % messageRows * lanes + lane.val
        have hoff : off < messageRows * lanes := by
          have hb := Nat.mod_lt row.val hrows
          dsimp [off]
          nlinarith
        (input.get ⟨off, by
          rw [hInput]
          simpa only [hLayout, Bool.false_eq_true, ite_false] using hoff⟩).val
    else 0

/-- Run a matched bit-plane encoding workload or stage digest fixture. -/
def main (args : List String) : IO UInt32 := do
  let mode :: layout :: rawD :: rawLive :: rawRate :: rest := args
    | throw <| IO.userError "expected mode layout domain live rate"
  let some d := rawD.toNat? | throw <| IO.userError "invalid domain"
  let some live := rawLive.toNat? | throw <| IO.userError "invalid lanes"
  let some rate := rawRate.toNat? | throw <| IO.userError "invalid rate"
  unless mode == "bench" || mode == "check" || mode == "dump" do
    throw <| IO.userError "mode must be bench, check or dump"
  let lanes := if layout == "k" then (live + 7) / 8 * 8 else 3 * live
  unless layout == "k" || layout == "e" do throw <| IO.userError "invalid layout"
  if hd : d < 64 then
   if hr : rate ≤ d then
    if hn : 8 * (2 ^ d * 64) < 4294967296 then
     if hl : 0 < lanes ∧ lanes ≤ 64 then
      let ell := d - rate
      have hell : ell ≤ d := by omega
      let setupStart ← IO.monoNanosNow
      let p := AdditiveNTT.Bitsliced.Plan.create flatBasis d hd
      let setupStop ← IO.monoNanosNow
      let input : BF64.Packed := if hLayout : layout == "k" then
        (tabulate (live * 2 ^ ell) fun i => seed i.val).val
        else (tabulate (2 ^ ell * lanes) fun i => seed i.val).val
      have hInput : input.size = (if layout == "k" then live * 2 ^ ell else 2 ^ ell * lanes) := by
        dsimp only [input]
        split
        · exact (tabulate (live * 2 ^ ell) fun i => seed i.val).property
        · exact (tabulate (2 ^ ell * lanes) fun i => seed i.val).property
      let makeInput : Unit → Rows (2 ^ d) := fun _ =>
        buildInput layout (2 ^ d) (2 ^ ell) live lanes hn input hInput (by positivity)
      let stdout ← IO.getStdout
      let stdin ← IO.getStdin
      if mode == "bench" then
        stdout.putStrLn s!"begin {setupStop - setupStart}"
        stdout.flush
        discard <| stdin.getLine
        let start ← IO.monoNanosNow
        let output := encode p ell hell hn makeInput
        let stop ← IO.monoNanosNow
        stdout.putStrLn s!"end {stop - start}"
        stdout.flush
        discard <| stdin.getLine
        let (lo, hi) := digest output lanes hl.2
        stdout.putStrLn s!"sink {lo}:{hi}"
        stdout.flush
      else
        let input := makeInput ()
        report "input" input hn lanes hl.2
        let mut output := input
        for hk : k in [:ell] do
          let i : Fin d := ⟨ell - k - 1, by have hklt : k < ell := hk.upper; omega⟩
          output := AdditiveNTT.Bitsliced.forwardStage p i output hn
          report s!"stage-{i.val}" output hn lanes hl.2
        report "output" output hn lanes hl.2
        let recovered := AdditiveNTT.Bitsliced.inverse p ell hell output hn
        unless recovered.val.bytes == input.val.bytes do
          throw <| IO.userError "inverse did not recover bit-plane input"
        if mode == "dump" then
          let [path] := rest | throw <| IO.userError "dump requires one output path"
          let words := transposeRows output hn
          let logical := tabulate (2 ^ d * lanes) fun j =>
            let row := j.val / lanes
            let col := j.val % lanes
            have hrow : row < 2 ^ d := (Nat.div_lt_iff_lt_mul hl.1).mpr j.isLt
            have hcol : col < 64 := lt_of_lt_of_le (Nat.mod_lt _ hl.1) hl.2
            BF64.Packed.read words ⟨row * 64 + col, by nlinarith⟩
          IO.FS.writeBinFile path logical.val.bytes
      pure 0
     else throw <| IO.userError "lanes must be within 1..64"
    else throw <| IO.userError "padded codeword must be smaller than four GiB"
   else throw <| IO.userError "rate exceeds domain"
  else throw <| IO.userError "domain must be below 64"
