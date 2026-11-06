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

/-- BF64 scalar kernels, with specification digests on the same inputs. -/
def bf64Tasks : List BenchTask :=
  [BenchTask.fromGroupRunner ⟨"fields-bf64-mul", "GF(2^64) multiplication"⟩ runBF64,
    BenchTask.fromGroupRunner ⟨"fields-bf64-fixed", "GF(2^64) shared multiplier"⟩ runFixed,
    BenchTask.fromGroupRunner ⟨"fields-bf64-ext3", "GF(2^192) multiplication"⟩ runExt3,
    BenchTask.fromGroupRunner ⟨"fields-bf64-masked", "GF(2^64) masked product"⟩ runMasked]

end CompPolyBench
