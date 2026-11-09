/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Plan
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Layout

/-!
# Additive NTT Benchmarks
-/

public section

open ConcreteBinaryTower

namespace CompPolyBench

/-- Checksum all output values from a `BTF₃` additive NTT benchmark. -/
private def checksumBtf3Output {n : Nat} (output : Fin (2 ^ n) → AdditiveNTT.BTF₃) : Nat :=
  (List.finRange (2 ^ n)).foldl
    (fun acc i ↦ mixChecksum acc (checksumBtf3 (output i))) 0

/-- Checksum a `BTF₃` additive NTT output array. -/
private def checksumBtf3OutputArray {n : Nat} (output : Array AdditiveNTT.BTF₃) : Nat :=
  checksumBtf3Output (AdditiveNTT.arrayToFinFunction (2 ^ n) output)

/-- Checksum a concrete binary-tower additive NTT output array. -/
private def checksumConcreteBtfOutputArray {k n : Nat} (output : Array (ConcreteBTField k)) :
    Nat :=
  let values := AdditiveNTT.arrayToFinFunction (2 ^ n) output
  (List.finRange (2 ^ n)).foldl
    (fun acc i ↦ mixChecksum acc (checksumConcreteBtf (values i))) 0

/-! ### Timed-region sinks

The reference row returns `Fin (2 ^ n) → α` — a *function*, so an output value
does not exist until an index is applied — while the fast row returns a
materialised `Array`. Realising the whole result is therefore part of the
reference row's work and not part of the fast row's, so both sinks fold over
every output position: sampling a few positions would leave the reference row
computing a fraction of what the fast row computes and the ratio would be
meaningless.

What these avoid, relative to the `Nat` digests above, is the bignum
`mixChecksum` and the per-iteration `List.finRange (2 ^ n)` materialisation. The
fold itself is a handful of machine instructions per output. -/

/-- Fold every position of a `Fin`-indexed output into a sink accumulator. -/
@[inline] private def sinkFinAll {m : Nat} (toNat : α → Nat) (output : Fin m → α) : UInt64 :=
  Nat.fold m (fun i h acc ↦ sinkStep acc (natSink (toNat (output ⟨i, h⟩)))) 0

/-- Fold every element of an output array into a sink accumulator. -/
@[inline] private def sinkArrayAll (toNat : α → Nat) (output : Array α) : UInt64 :=
  output.foldl (fun acc x ↦ sinkStep acc (natSink (toNat x))) 0

/-- Sink a `BTF₃` additive NTT output function. -/
@[inline] private def sinkBtf3Output {n : Nat} (output : Fin (2 ^ n) → AdditiveNTT.BTF₃) :
    UInt64 :=
  sinkFinAll checksumBtf3 output

/-- Sink a `BTF₃` additive NTT output array. -/
@[inline] private def sinkBtf3OutputArray (output : Array AdditiveNTT.BTF₃) : UInt64 :=
  sinkArrayAll checksumBtf3 output

/-- Sink a concrete binary-tower additive NTT output array. -/
@[inline] private def sinkConcreteBtfOutputArray {k : Nat} (output : Array (ConcreteBTField k)) :
    UInt64 :=
  sinkArrayAll checksumConcreteBtf output

/-- Run an additive NTT over `BTF₃`. -/
private def runBtf3Ntt (ℓ R_rate : Nat) (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ 3)
    (input : Fin (2 ^ ℓ) → AdditiveNTT.BTF₃) :
    Fin (2 ^ (ℓ + R_rate)) → AdditiveNTT.BTF₃ := by
  letI : Algebra (ConcreteBTField 0) AdditiveNTT.BTF₃ :=
    ConcreteBTFieldAlgebra (l := 0) (r := 3) (h_le := by omega)
  haveI : Fact (LinearIndependent (ConcreteBTField 0) (AdditiveNTT.computableBasisExplicit 3)) :=
    { out := AdditiveNTT.hβ_lin_indep_concrete 3 }
  exact AdditiveNTT.computableAdditiveNTT
    (𝔽q := ConcreteBTField 0) (L := AdditiveNTT.BTF₃) (r := 2 ^ 3)
    (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (β := AdditiveNTT.computableBasisExplicit (k := 3)) (a := input)

/-- Run the fast additive NTT implementation over `BTF₃`. -/
private def runBtf3NttFast (ℓ R_rate : Nat) (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ 3)
    (input : Fin (2 ^ ℓ) → AdditiveNTT.BTF₃) :
    Array AdditiveNTT.BTF₃ := by
  letI : Algebra (ConcreteBTField 0) AdditiveNTT.BTF₃ :=
    ConcreteBTFieldAlgebra (l := 0) (r := 3) (h_le := by omega)
  exact AdditiveNTT.computableAdditiveNTTFast
    (L := AdditiveNTT.BTF₃) (r := 2 ^ 3)
    (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (β := AdditiveNTT.computableBasisExplicit (k := 3)) (a := input)

/-- Run the fast additive NTT implementation over a concrete binary-tower field. -/
private def runConcreteBtfNttFast (k ℓ R_rate : Nat)
    (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ k)
    (input : Fin (2 ^ ℓ) → ConcreteBTField k) :
    Array (ConcreteBTField k) := by
  letI : Fintype (ConcreteBTField k) :=
    Fintype.ofEquiv (Fin (2 ^ (2 ^ k)))
      ((ConcreteBTField.equivBitVec k).trans (BitVec.equivFin (m := 2 ^ k))).symm
  letI : Algebra (ConcreteBTField 0) (ConcreteBTField k) :=
    ConcreteBTFieldAlgebra (l := 0) (r := k) (h_le := by omega)
  exact AdditiveNTT.computableAdditiveNTTFast
    (L := ConcreteBTField k) (r := 2 ^ k)
    (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (β := AdditiveNTT.computableBasisExplicit (k := k)) (a := input)

/-- Run one additive NTT benchmark pair over `BTF₃`. -/
private def runAdditiveNttCase (ℓ R_rate : Nat) (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ 3)
    (key currentName fastName : String)
    (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let inputSize := 2 ^ ℓ
  let outputSize := 2 ^ (ℓ + R_rate)
  let (values, gen) := (randomNatArray inputSize 255).run gen
  let input : Fin (2 ^ ℓ) → AdditiveNTT.BTF₃ :=
    fun i ↦ ConcreteBinaryTower.fromNat (k := 3) (values.getD i.val 0)
  let fieldLabel := s!"ConcreteBTField 0 -> BTF3, l={ℓ}, R_rate={R_rate}"
  let inputShape := s!"{inputSize} input coeffs, {outputSize} output evals"
  let checksumIterations := digestPeriod 1
  let currentRecord ← runTimedSpec
    { name := currentName, representation := "computableAdditiveNTT",
      method := "computableAdditiveNTT", field := fieldLabel, inputShape := inputShape,
      digestIterations := checksumIterations }
    preset (fun _ ↦ runBtf3Ntt ℓ R_rate h_ℓ_add_R_rate input)
    (checksumBtf3Output (n := ℓ + R_rate)) (sink := sinkBtf3Output)
  let fastRecord ← runTimedSpec
    { name := fastName, representation := "computableAdditiveNTTFast",
      method := "computableAdditiveNTTFast", field := fieldLabel, inputShape := inputShape,
      digestIterations := checksumIterations }
    preset (fun _ ↦ runBtf3NttFast ℓ R_rate h_ℓ_add_R_rate input)
    (checksumBtf3OutputArray (n := ℓ + R_rate)) (sink := sinkBtf3OutputArray)
  pure ({
      groupKey := key,
      title := s!"Additive NTT BTF3 l={ℓ} R_rate={R_rate}",
      records := #[currentRecord, fastRecord] }, gen)

/-- Run one fast-only additive NTT benchmark over a concrete binary-tower field. -/
private def runAdditiveNttFastLargeCase (k ℓ R_rate : Nat)
    (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ k) (key fastName : String)
    (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let inputSize := 2 ^ ℓ
  let outputSize := 2 ^ (ℓ + R_rate)
  let (values, gen) := (randomNatArray inputSize (2 ^ (2 ^ k) - 1)).run gen
  let input : Fin (2 ^ ℓ) → ConcreteBTField k :=
    fun i ↦ ConcreteBinaryTower.fromNat (k := k) (values.getD i.val 0)
  let fieldLabel := s!"ConcreteBTField 0 -> BTF{k}, l={ℓ}, R_rate={R_rate}"
  let inputShape := s!"{inputSize} input coeffs, {outputSize} output evals"
  let fastRecord ← runTimedSpec
    { name := fastName, representation := "computableAdditiveNTTFast",
      method := "computableAdditiveNTTFast", field := fieldLabel, inputShape := inputShape,
      digestIterations := digestPeriod 1 }
    preset (fun _ ↦ runConcreteBtfNttFast k ℓ R_rate h_ℓ_add_R_rate input)
    (checksumConcreteBtfOutputArray (k := k) (n := ℓ + R_rate)) (sink := sinkConcreteBtfOutputArray)
  pure ({
      groupKey := key,
      title := s!"Additive NTT BTF{k} l={ℓ} R_rate={R_rate}",
      records := #[fastRecord] }, gen)

/-- Run the `BTF₃` additive NTT benchmark with `ℓ = 2` and `R_rate = 2`. -/
private def runAdditiveNttBtf3L2R2 (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runAdditiveNttCase 2 2 (by omega)
    "additive-ntt-btf3-l2-r2" "additive-ntt-btf3" "additive-ntt-btf3-fast" preset gen

/-- Run the `BTF₃` additive NTT benchmark with `ℓ = 4` and `R_rate = 2`. -/
private def runAdditiveNttBtf3L4R2 (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runAdditiveNttCase 4 2 (by omega)
    "additive-ntt-btf3-l4-r2" "additive-ntt-btf3-l4-r2"
    "additive-ntt-btf3-l4-r2-fast" preset gen

/-- Run the `BTF₄` fast-only additive NTT benchmark with `ℓ = 7` and `R_rate = 2`. -/
private def runAdditiveNttBtf4L7R2 (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runAdditiveNttFastLargeCase 4 7 2 (by omega)
    "additive-ntt-btf4-l7-r2" "additive-ntt-btf4-l7-r2-fast" preset gen

/-- Consume every retained row coordinate and byte-table entry. -/
private def sinkPackedPlan (tables : Array (Sigma AdditiveNTT.Packed.TwiddleRow)) : UInt64 :=
  tables.foldl (fun acc row =>
    let acc := row.2.values.toArray.foldl (fun acc word => sinkStep acc word.val) acc
    row.2.tables.toArray.foldl (fun acc table =>
      table.toArray.foldl (fun acc word => sinkStep acc word.val) acc) acc) 0

/-- Measure complete scalar-plan preparation at alternating output-dependent domains. -/
private def runPackedTwiddlePlan (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let record ← runTimedSpec
    { name := "additive-ntt-packed-plan", representation := "compact scalar plan",
      method := "Plan.create", field := "BF64", inputShape := "log domains 6 and 7",
      digestIterations := 2 }
    preset (fun iteration =>
      let d := 6 + iteration % 2
      (AdditiveNTT.Bitsliced.Plan.create AdditiveNTT.Packed.flatBasis d (by omega)).stages.toArray)
    (fun tables => (sinkPackedPlan tables).toNat) (sink := sinkPackedPlan)
  pure ({
    groupKey := "additive-ntt-packed-plan",
    title := "Packed additive plan preparation",
    records := #[record] }, gen)

/-- Measure complete word-row encoding with an output-dependent input. -/
private def runWordRows (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let plan := AdditiveNTT.Bitsliced.Plan.create AdditiveNTT.Packed.flatBasis 8 (by decide)
  let record ← runTimedSpec
    { name := "additive-ntt-word-rows", representation := "64 packed word lanes",
      method := "encode", field := "BF64", inputShape := "log domain 8, log rate 1",
      digestIterations := 2 }
    preset (fun iteration =>
      let input := AdditiveNTT.Packed.tabulate (2 ^ 8 * 64) fun i =>
        (⟨(UInt64.ofNat (i.val + iteration) + 1) * 0x9e3779b97f4a7c15⟩ : BF64.Word)
      (AdditiveNTT.Bitsliced.encode plan 7 (by decide) input (by decide)).val.bytes)
    (fun bytes => (bytes.foldl (fun acc byte => sinkStep acc byte.toUInt64) 0).toNat)
    (sink := fun bytes => bytes.foldl (fun acc byte => sinkStep acc byte.toUInt64) 0)
  pure ({
    groupKey := "additive-ntt-word-rows",
    title := "Packed additive word-row encoding",
    records := #[record] }, gen)

/-- Runnable additive-NTT benchmark tasks. -/
def additiveNttTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"additive-ntt-btf3-l2-r2", "Additive NTT BTF3 l=2 R_rate=2"⟩
    runAdditiveNttBtf3L2R2,
  BenchTask.fromGroupRunner
    ⟨"additive-ntt-btf3-l4-r2", "Additive NTT BTF3 l=4 R_rate=2"⟩
    runAdditiveNttBtf3L4R2,
  BenchTask.fromGroupRunner
    ⟨"additive-ntt-btf4-l7-r2", "Additive NTT BTF4 l=7 R_rate=2"⟩
    runAdditiveNttBtf4L7R2,
  BenchTask.fromGroupRunner
    ⟨"additive-ntt-packed-plan", "Packed additive plan preparation"⟩
    runPackedTwiddlePlan,
  BenchTask.fromGroupRunner
    ⟨"additive-ntt-word-rows", "Packed additive word-row encoding"⟩
    runWordRows
]

end CompPolyBench
