/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Layout
/-! # Counter-marked decomposition of the bit-plane butterfly -/
public section
open AdditiveNTT.Bitsliced BF64

private def seed (i : Nat) : UInt64 :=
  0x0123456789abcdef ^^^ ((UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15)

@[noinline] private def loopChain : Nat → UInt64 → UInt64
  | 0, t => t
  | n + 1, t => loopChain n (t + 1)

@[noinline] private def matrixChain : Nat → UInt64 → UInt64
  | 0, t => t
  | n + 1, t => matrixChain n ((matrix t).w63 + 1)

@[noinline] private def transposeChain : Nat → Block → Block
  | 0, a => a
  | n + 1, a => transposeChain n (transpose a)

@[noinline] private def prepareChain : Nat → Block → Scratch → Scratch
  | 0, _, s => s
  | n + 1, a, s => prepareChain n a (prepareScratch s a)

@[noinline] private def applyChain : Nat → Scratch → Block → Block
  | 0, _, m => m
  | n + 1, s, m => applyChain n s (applyScratch s m)

@[noinline] private def xorChain : Nat → Block → Block → Block → Block × Block
  | 0, _, u, v => (u, v)
  | n + 1, m, u, v =>
    let lo := u.xor m
    xorChain n m lo (lo.xor v)

@[noinline] private def kernelChain : Nat → Block → Block → Block → Scratch → Block × Block
  | 0, _, u, v, _ => (u, v)
  | n + 1, m, u, v, s =>
    let out := forwardKernel m u v s
    kernelChain n m out.1.1 out.1.2 out.2

@[noinline] private def moveChain : Nat → Rows 2 → Rows 2
  | 0, a => a
  | n + 1, a =>
    let u := Native.load a (by decide) 0 (by decide)
    let v := Native.load a (by decide) 64 (by simp only [Native.small 64 (by decide)]; omega)
    moveChain n (Native.store (Native.store a (by decide) 0 (by decide) v)
      (by decide) 64 (by simp only [Native.small 64 (by decide)]; omega) u)

@[noinline] private def stageChain (identity : Bool)
    (p : Plan AdditiveNTT.Packed.flatBasis 16 (by decide))
    (i : Fin 16) : Nat → Rows 65536 → Rows 65536
  | 0, a => a
  | n + 1, a =>
    let a := if identity then
      stageSweep (fun _ u v s => ((u, v), s)) p i a (by decide)
      else forwardStage p i a (by decide)
    stageChain identity p i n a

/-- Execute one isolated operation chain between inherited-counter handshakes. -/
def main (args : List String) : IO Unit := do
  let [mode, part, rawN] := args | throw <| IO.userError "expected bench part count"
  unless mode == "bench" do throw <| IO.userError "expected bench"
  let some n := rawN.toNat? | throw <| IO.userError "invalid count"
  let a := Block.ofFn fun i => seed i.val
  let v := transpose a
  let m := matrix (seed 67)
  let s := prepareScratch ⟨ByteArray.zeros 2048, ByteArray.size_zeros _⟩ v
  let words := fromFn 2 (by decide) fun r c => seed (r.val * 64 + c.val)
  let p := Plan.create AdditiveNTT.Packed.flatBasis 16 (by decide)
  let rows := fromFn 65536 (by decide) fun r c => seed (r.val * 64 + c.val)
  let stdout ← IO.getStdout
  let stdin ← IO.getStdin
  stdout.putStrLn "begin 0"
  stdout.flush
  discard <| stdin.getLine
  let start ← IO.monoNanosNow
  let sink ← match part with
    | "loop" => pure (loopChain n (seed 0))
    | "matrix" => pure (matrixChain n (seed 67))
    | "transpose" => pure (transposeChain n v).w0
    | "prepare" =>
      pure ((prepareChain n v s).read 8 (by simp only [Native.small 8 (by decide)]; omega))
    | "apply" => pure (applyChain n s m).w0
    | "xor" =>
      let out := xorChain n m a v
      pure (out.1.w0 + out.2.w63)
    | "kernel" => pure (kernelChain n m a v s).1.w0
    | "move" => pure (Native.read (moveChain n words) (by decide) 0 (by decide))
    | "stage-0" => pure (Native.read (stageChain false p 0 n rows) (by decide) 0 (by decide))
    | "stage-8" => pure (Native.read (stageChain false p 8 n rows) (by decide) 0 (by decide))
    | "stage-15" => pure (Native.read (stageChain false p 15 n rows) (by decide) 0 (by decide))
    | "identity-0" => pure (Native.read (stageChain true p 0 n rows) (by decide) 0 (by decide))
    | "identity-8" => pure (Native.read (stageChain true p 8 n rows) (by decide) 0 (by decide))
    | "identity-15" => pure (Native.read (stageChain true p 15 n rows) (by decide) 0 (by decide))
    | _ => throw <| IO.userError "invalid part"
  let stop ← IO.monoNanosNow
  stdout.putStrLn s!"end {stop - start}"
  stdout.flush
  discard <| stdin.getLine
  stdout.putStrLn s!"sink {sink}"
  stdout.flush
