/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import CompPoly.Fields.Binary.BF64.Word
import CompPoly.Fields.Binary.BF64.MaskedOps
import CompPoly.Fields.Binary.BF64.FixedMap
import CompPoly.Fields.Binary.BF64.WordExt3Dot
import CompPoly.Fields.Binary.BF64.WordExt3Frobenius
import CompPoly.Fields.Binary.BF64.Masked
import CompPolyBench.Harness.Chain
import CompPolyBench.Fields.Binary.BF64Bitslice

/-!
# Instruction-count runner for binary-field kernels

The driver acknowledges a start marker before entering the measured phase.
The sink is printed with the end marker. Module initialization and fixture
construction are excluded from hardware-counter measurements.
-/

public section

open BF64 CompPolyBench

@[noinline] private def scalarChain : Nat → UInt64 → UInt64 → UInt64
  | 0, a, _ => a
  | n + 1, a, b => scalarChain n (Word.mul ⟨a⟩ ⟨b⟩).val b

@[noinline] private def maskedChain : Nat → UInt64 → UInt64 → UInt64
  | 0, a, _ => a
  | n + 1, a, b => maskedChain n (Word.mulMasked ⟨a⟩ ⟨b⟩).val b

@[noinline] private def specChain : Nat → BF64 → BF64 → BF64
  | 0, a, _ => a
  | n + 1, a, b => specChain n (a * b) b

@[noinline] private def nibbleChain (n : Nat) (m : Word.NibbleMap) (a : UInt64) : UInt64 :=
  match n with
  | 0 => a
  | n + 1 => nibbleChain n m (m.mul ⟨a⟩).val

@[noinline] private def byteChain (n : Nat) (m : Word.ByteMap) (a : UInt64) : UInt64 :=
  match n with
  | 0 => a
  | n + 1 => byteChain n m (m.mul ⟨a⟩).val

@[inline] private def extSink (a : WordExt3) : UInt64 :=
  a.c0.val ^^^ a.c1.val ^^^ a.c2.val

@[noinline] private def extChain : Nat → WordExt3 → WordExt3 → WordExt3
  | 0, a, _ => a
  | n + 1, a, b => extChain n (WordExt3.mul a b) b

@[specialize] private def unaryChain (op : Word → Word) : Nat → UInt64 → UInt64
  | 0, a => a
  | n + 1, a => unaryChain op n (op ⟨a ^^^ 0x9e3779b97f4a7c15⟩).val

@[specialize] private def extUnaryChain (op : WordExt3 → WordExt3) :
    Nat → WordExt3 → WordExt3
  | 0, a => a
  | n + 1, a => extUnaryChain op n (op (WordExt3.add a
      ⟨⟨0x9e3779b97f4a7c15⟩, ⟨0x1122334455667788⟩, ⟨0x8000000000000001⟩⟩))

private def dotReduced (a b : WordExt3.Buffer 64) : WordExt3 :=
  (List.finRange 64).foldl (fun acc i => WordExt3.add acc
    (WordExt3.mul (WordExt3.read a i) (WordExt3.read b i))) ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

@[noinline] private def dotReducedChain (a b : WordExt3.Buffer 64) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | n + 1, acc =>
    let r := dotReduced (Packed.write a ⟨0, by decide⟩ ⟨acc⟩) b
    dotReducedChain a b n (acc ^^^ extSink r)

@[noinline] private def dotChain (a b : WordExt3.Buffer 64) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | n + 1, acc =>
    let r := WordExt3.dot (Packed.write a ⟨0, by decide⟩ ⟨acc⟩) b
    dotChain a b n (acc ^^^ extSink r)

@[noinline] private def nibbleBuildChain : Nat → UInt64 → UInt64 → UInt64
  | 0, a, _ => a
  | n + 1, a, b =>
    nibbleBuildChain n ((Word.NibbleMap.ofScalar ⟨a⟩).mul ⟨b⟩).val b

@[noinline] private def byteBuildChain : Nat → UInt64 → UInt64 → UInt64
  | 0, a, _ => a
  | n + 1, a, b =>
    byteBuildChain n ((Word.ByteMap.ofScalar ⟨a⟩).mul ⟨b⟩).val b

/-- Run one named kernel phase; the Python driver supplies the operation count. -/
def main (args : List String) : IO UInt32 := do
  let [op, rawN] := args | throw <| IO.userError "expected operation and count"
  let some n := rawN.toNat? | throw <| IO.userError "invalid count"
  let stdout ← IO.getStdout
  let stdin ← IO.getStdin
  let a : UInt64 := 0x0123456789abcdef
  let b : UInt64 := 0xfedcba9876543210
  let nibble := Word.NibbleMap.ofScalar ⟨b⟩
  let byte := Word.ByteMap.ofScalar ⟨b⟩
  let lanesA := (Array.range 64).map fun i => a ^^^ (UInt64.ofNat i * b)
  let lanesB := (Array.range 64).map fun i => b ^^^ (UInt64.ofNat i * a)
  let ea : WordExt3 := ⟨⟨a⟩, ⟨b⟩, ⟨a ^^^ b⟩⟩
  let da := WordExt3.ofFn 64 fun i =>
    ⟨⟨a ^^^ UInt64.ofNat i.val⟩, ⟨b⟩, ⟨a ^^^ b⟩⟩
  let db := WordExt3.ofFn 64 fun i =>
    ⟨⟨b ^^^ UInt64.ofNat i.val⟩, ⟨a⟩, ⟨b ^^^ 0x1122334455667788⟩⟩
  if op == "bitslice" then
    let got := BF64Bitslice.mul lanesA lanesB
    for i in [0:64] do
      unless got[i]! == (Word.mul ⟨lanesA[i]!⟩ ⟨lanesB[i]!⟩).val do
        throw <| IO.userError "bitslice differential mismatch"
  stdout.putStrLn "begin"
  stdout.flush
  discard <| stdin.getLine
  let start ← IO.monoNanosNow
  let result ← match op with
    | "masked-square" => pure <| unaryChain Word.squareMasked n a
    | "masked-inverse" => pure <| unaryChain Word.invMasked n a
    | "masked-frobenius" => pure <| unaryChain (fun x => Word.frobeniusMasked x 8) n a
    | "dot64-reduced" => pure <| dotReducedChain da db (n / 64) a
    | "square" => pure <| unaryChain Word.square n a
    | "inverse" => pure <| unaryChain Word.inv n a
    | "frobenius" => pure <| unaryChain (fun x => Word.frobenius x 8) n a
    | "ext-qfrobenius" => pure <| extSink (extUnaryChain WordExt3.frobeniusK n ea)
    | "ext-square" => pure <| extSink (extUnaryChain WordExt3.square n ea)
    | "ext-frobenius" => pure (extSink (extUnaryChain
        (fun x => WordExt3.frobenius x 64) n ea))
    | "mixed" => pure (extSink (extUnaryChain
        (fun x => WordExt3.mulScalar x ⟨b⟩) n ea))
    | "dot64" => pure <| dotChain da db (n / 64) a
    | "bitslice" => pure <| (BF64Bitslice.chain (n / 64) lanesA lanesB)[0]!
    | "masked-throughput" => pure (chainThroughput
          (fun a b : UInt64 => (Word.mulMasked ⟨a⟩ ⟨b⟩).val) (· ^^^ ·) (n / 10)
          a b (a ^^^ 2) (b ^^^ 3) (a ^^^ 4) (b ^^^ 5) (a ^^^ 6) (b ^^^ 7)
          (a ^^^ 8) (b ^^^ 9))
    | "ext3" => pure <| extSink (extChain n ⟨⟨a⟩, ⟨b⟩, ⟨a ^^^ b⟩⟩
        ⟨⟨b⟩, ⟨a⟩, ⟨b ^^^ 0x1122334455667788⟩⟩)
    | "nibble-build" => pure <| nibbleBuildChain n a b
    | "byte-build" => pure <| byteBuildChain n a b
    | "nibble" => pure <| nibbleChain n nibble a
    | "byte" => pure <| byteChain n byte a
    | "masked" => pure <| maskedChain n a b
    | "scalar" => pure <| scalarChain n a b
    | "spec" => pure <| UInt64.ofBitVec (specChain n (Word.toField ⟨a⟩)
        (Word.toField ⟨b⟩)).toBitVec
    | "throughput" => pure (chainThroughput
          (fun a b : UInt64 => (Word.mul ⟨a⟩ ⟨b⟩).val) (· ^^^ ·) (n / 10)
          a b (a ^^^ 2) (b ^^^ 3) (a ^^^ 4) (b ^^^ 5) (a ^^^ 6) (b ^^^ 7)
          (a ^^^ 8) (b ^^^ 9))
    | _ => throw <| IO.userError s!"unknown operation {op}"
  let stop ← IO.monoNanosNow
  stdout.putStrLn s!"end {stop - start} {result}"
  stdout.flush
  discard <| stdin.getLine
  pure 0
