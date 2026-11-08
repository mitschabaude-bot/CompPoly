/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Fields.Arith
public import CompPoly.Fields.Binary.BF64.Word
public import CompPoly.Fields.Binary.BF64.Masked
public import CompPoly.Fields.Binary.BF64.FixedMap
public import CompPoly.Fields.Binary.BF64.WordExt3
public import CompPoly.Fields.Binary.BF64.WordExt3Dot
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Butterfly

/-! # Polynomial-basis binary-field kernel benchmarks -/

public section

namespace CompPolyBench

open BF64

private def runBF64 (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (xs, gen) := (randomNatArray fieldPoolSize (2 ^ 64 - 3)).run gen
  let pool := xs.map fun x => Word.mk (UInt64.ofNat (x + 2))
  let fast : ChainRep Word :=
    { representation := "UInt64 shift/XOR", field := "BF64.Word", suffix := "word",
      pool, constant := pool[0]!, checksum := fun x => x.val.toNat, sink := Word.val }
  let slow : ChainRep BF64 :=
    { representation := "BitVec quotient carrier", field := "BF64", suffix := "spec",
      pool := pool.map Word.toField, constant := fast.constant.toField,
      checksum := fun x => x.toBitVec.toNat, sink := fun x => UInt64.ofBitVec x.toBitVec }
  let group ← runBinOpGroup "fields-bf64-mul" "GF(2^64) polynomial-basis multiplication"
    "bf64" "mul" heavyChainRounds heavyThroughputRounds slow (· * ·) fast Word.mul preset
  pure (group, gen)

private def runFixed (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (xs, gen) := (randomNatArray fieldPoolSize (2 ^ 64 - 3)).run gen
  let pool := xs.map fun x => Word.mk (UInt64.ofNat (x + 2))
  let scalar := pool[0]!
  let rep : ChainRep Word :=
    { representation := "UInt64 shift/XOR", field := "BF64.Word", suffix := "word",
      pool, constant := scalar, checksum := fun x => x.val.toNat, sink := Word.val }
  let nibble := Word.NibbleMap.ofScalar scalar
  let byte := Word.ByteMap.ofScalar scalar
  let scalarRow ← chainLatencyRow "bf64" "fixed" "scalar" "fixed" chainRounds rep
    (fun a => Word.mul scalar a) preset
  let nibbleRow ← chainLatencyRow "bf64" "fixed" "nibble (2 KiB)" "fixed" chainRounds
    { rep with suffix := "nibble", representation := "packed nibble map" } nibble.mul preset
  let byteRow ← chainLatencyRow "bf64" "fixed" "byte (16 KiB)" "fixed" chainRounds
    { rep with suffix := "byte", representation := "packed byte map" } byte.mul preset
  let group : BenchGroup :=
    { groupKey := "fields-bf64-fixed", title := "GF(2^64) shared-multiplier maps",
      records := #[scalarRow, nibbleRow, byteRow] }
  pure (group, gen)

private def runTwiddle (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (xs, gen) := (randomNatArray fieldPoolSize (2 ^ 64 - 3)).run gen
  let pool := xs.map fun x => Word.mk (UInt64.ofNat (x + 2))
  let scalar := pool[0]!
  let rep : ChainRep Word :=
    { representation := "certified shared twiddle", field := "BF64.Word", suffix := "prepared",
      pool, constant := scalar, checksum := fun x => x.val.toNat, sink := Word.val }
  let prepared := AdditiveNTT.Packed.Multiplier.prepared scalar
  let direct := AdditiveNTT.Packed.Multiplier.masked scalar
  let preparedRow ← chainLatencyRow "bf64" "twiddle" "prepared" "twiddle" chainRounds rep
    prepared.apply preset
  let directRow ← chainLatencyRow "bf64" "twiddle" "direct" "twiddle" chainRounds
    { rep with suffix := "direct" } direct.apply preset
  pure ({ groupKey := "fields-bf64-twiddle", title := "Shared additive twiddle",
          records := #[preparedRow, directRow] }, gen)

private def runExt3 (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (xs, gen) := (randomNatArray (3 * fieldPoolSize) (2 ^ 64 - 3)).run gen
  let pool := (Array.range fieldPoolSize).map fun i =>
    WordExt3.mk ⟨UInt64.ofNat (xs[3*i]! + 2)⟩ ⟨UInt64.ofNat (xs[3*i+1]! + 2)⟩
      ⟨UInt64.ofNat (xs[3*i+2]! + 2)⟩
  let fast : ChainRep WordExt3 :=
    { representation := "three UInt64 coordinates", field := "BF64.WordExt3", suffix := "word",
      pool, constant := pool[0]!, checksum := fun x =>
        x.c0.val.toNat + 2^64*x.c1.val.toNat + 2^128*x.c2.val.toNat,
      sink := fun x => x.c0.val ^^^ x.c1.val ^^^ x.c2.val }
  let slow : ChainRep BF64.Ext3 :=
    { representation := "generic cubic extension", field := "BF64.Ext3", suffix := "spec",
      pool := pool.map WordExt3.toField, constant := fast.constant.toField,
      checksum := fun x => fast.checksum (WordExt3.ofField x),
      sink := fun x => fast.sink (WordExt3.ofField x) }
  let group ← runBinOpGroup "fields-bf64-ext3" "GF(2^192) cubic multiplication"
    "bf64-ext3" "mul" heavyChainRounds heavyThroughputRounds slow (· * ·)
    fast WordExt3.mul preset
  pure (group, gen)

private def runMasked (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (xs, gen) := (randomNatArray fieldPoolSize (2 ^ 64 - 3)).run gen
  let pool := xs.map fun x => Word.mk (UInt64.ofNat (x + 2))
  let scalar : ChainRep Word :=
    { representation := "UInt64 shift/XOR", field := "BF64.Word", suffix := "scalar",
      pool, constant := pool[0]!, checksum := fun x => x.val.toNat, sink := Word.val }
  let masked : ChainRep Word :=
    { scalar with representation := "masked integer multiplication", suffix := "masked" }
  let group ← runBinOpGroup "fields-bf64-masked" "GF(2^64) masked integer multiplication"
    "bf64-masked" "mul" chainRounds throughputRounds scalar Word.mul
    masked Word.mulMasked preset
  pure (group, gen)

private def runDot (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (xs, gen) := (randomNatArray (6 * 64) (2 ^ 64 - 3)).run gen
  let element (offset i : Nat) : WordExt3 :=
    ⟨⟨UInt64.ofNat (xs[offset + 3*i]! + 2)⟩, ⟨UInt64.ofNat (xs[offset + 3*i+1]! + 2)⟩,
      ⟨UInt64.ofNat (xs[offset + 3*i+2]! + 2)⟩⟩
  let a := WordExt3.ofFn 64 fun i => element 0 i.val
  let b := WordExt3.ofFn 64 fun i => element (3*64) i.val
  let reduced (a b : WordExt3.Buffer 64) :=
    (List.finRange 64).foldl (fun acc i => WordExt3.add acc
      (WordExt3.mul (WordExt3.read a i) (WordExt3.read b i))) ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩
  let checksum (x : WordExt3) := x.c0.val.toNat + 2^64*x.c1.val.toNat + 2^128*x.c2.val.toNat
  let sink (x : WordExt3) := x.c0.val ^^^ x.c1.val ^^^ x.c2.val
  let mut records := #[]
  for (name, f) in [("reduced", reduced), ("deferred", WordExt3.dot)] do
    let row ← runTimedSpec
      { name := "bf64-ext3-dot-" ++ name, representation := "packed three-word coordinates",
        method := name ++ " dot", field := "BF64.WordExt3", inputShape := "64 extension products",
        workUnits := 64, digestIterations := 4, digestClass := "dot64" }
      preset (fun iteration =>
        f (Packed.write a ⟨0, by decide⟩ ⟨UInt64.ofNat (iteration % 4) ^^^ 0x123456789abcdef⟩) b)
      checksum (sink := sink)
    records := records.push row
  let group : BenchGroup :=
    { groupKey := "fields-bf64-ext3-dot", title := "Packed cubic-extension dots", records }
  pure (group, gen)

private def runMapSetup (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let mut records := #[]
  for (name, f) in [("nibble", fun a => (Word.NibbleMap.ofScalar a).mul ⟨0xfedcba9876543210⟩),
      ("byte", fun a => (Word.ByteMap.ofScalar a).mul ⟨0xfedcba9876543210⟩)] do
    let row ← runTimedSpec
      { name := "bf64-map-setup-" ++ name, representation := "packed shared-scalar map",
        method := name ++ " setup and product", field := "BF64.Word", inputShape := "one scalar",
        digestIterations := 4, digestClass := "setup" }
      preset (fun iteration => f ⟨UInt64.ofNat (iteration % 4) ^^^ 0x123456789abcdef⟩)
      (fun x => x.val.toNat) (sink := Word.val)
    records := records.push row
  let group : BenchGroup :=
    { groupKey := "fields-bf64-map-setup", title := "Shared-scalar map preparation", records }
  pure (group, gen)

/-- BF64 scalar kernels, with specification digests on the same inputs. -/
def bf64Tasks : List BenchTask :=
  [BenchTask.fromGroupRunner ⟨"fields-bf64-mul", "GF(2^64) multiplication"⟩ runBF64,
    BenchTask.fromGroupRunner ⟨"fields-bf64-fixed", "GF(2^64) shared multiplier"⟩ runFixed,
    BenchTask.fromGroupRunner ⟨"fields-bf64-twiddle", "Shared additive twiddle"⟩ runTwiddle,
    BenchTask.fromGroupRunner ⟨"fields-bf64-ext3", "GF(2^192) multiplication"⟩ runExt3,
    BenchTask.fromGroupRunner ⟨"fields-bf64-masked", "GF(2^64) masked product"⟩ runMasked,
    BenchTask.fromGroupRunner ⟨"fields-bf64-ext3-dot", "Packed cubic-extension dots"⟩ runDot,
    BenchTask.fromGroupRunner
      ⟨"fields-bf64-map-setup", "Shared-scalar map preparation"⟩ runMapSetup]

end CompPolyBench
