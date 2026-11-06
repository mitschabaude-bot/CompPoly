/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPolyBench.Fields.Arith
public import CompPoly.Fields.Binary.BF64

/-! # Polynomial-basis BF64 arithmetic benchmarks -/

public section

namespace CompPolyBench

private def runBF64Mul (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (words, gen) := (randomNatArray fieldPoolSize (2 ^ 64 - 3)).run gen
  let pool := words.map fun n ↦ BF64.ofBitVec (BitVec.ofNat 64 (n + 2))
  let rep : ChainRep BF64 :=
    { representation := "BF64 polynomial basis", field := "GF(2^64)", suffix := "binary",
      pool, constant := pool.getD 0 1,
      checksum := fun x ↦ x.toBitVec.toNat, sink := fun x ↦ natSink x.toBitVec.toNat }
  let row ← chainLatencyRow "bf64" "mul" "mul (latency)" "latency" 64 rep
    (fun x ↦ x * rep.constant) preset
  let group : BenchGroup :=
    { groupKey := "fields-bf64-mul", title := "Polynomial-basis BF64 multiplication",
      records := #[row] }
  return (group, gen)

/-- BF64 operations used by the binary-field GS decoder. -/
def bf64Tasks : List BenchTask :=
  [BenchTask.fromGroupRunner
    ⟨"fields-bf64-mul", "Polynomial-basis BF64 multiplication"⟩ runBF64Mul]

end CompPolyBench
