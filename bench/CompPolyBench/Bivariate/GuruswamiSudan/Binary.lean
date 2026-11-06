/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.Binary.BF64.GuruswamiSudan

/-! # Binary-field GS setup benchmarks -/

public section

namespace CompPolyBench

open CompPoly CompPoly.GuruswamiSudan

private def runMonomials (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (bounds, gen) := (randomNatArray 2 2).run gen
  let checksum := fun (xs : Array CBivariate.Monomial) ↦
    checksumArray (fun m ↦ mixChecksum m.xDegree m.yDegree) xs
  let mut records := #[]
  for (label, enumerate) in
      [("decoder", interpolationMonomials),
       ("grid", fun params ↦ ((CBivariate.monomialGrid params.weightedDegreeBound).filter
         fun m ↦ m.xDegree + yWeight params * m.yDegree ≤ params.weightedDegreeBound).toArray)] do
    let row ← runTimedSpec
      { name := s!"gs-monomials-{label}", representation := "Array Monomial",
        method := label, field := "Nat", inputShape := "k=3,D=127..129",
        digestIterations := 2, digestClass := "basis" }
      preset
      (fun i ↦ enumerate ⟨3, 1, 127 + bounds.getD (i % 2) 0⟩) checksum
      (sink := fun xs ↦ xs.foldl
        (fun acc m ↦ sinkStep acc (natSink (m.xDegree + 257 * m.yDegree))) 0)
    records := records.push row
  return (⟨"gs-interpolation-monomials", "GS weighted monomial enumeration", records⟩, gen)

private def runVanishing (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (offsets, gen) := (randomNatArray 2 1000).run gen
  let pool := offsets.map fun offset ↦ (Array.range 32).map fun i ↦
    BF64.ofBitVec (BitVec.ofNat 64 (i + 32 * offset))
  let mut records := #[]
  for (label, mul) in
      [("decoder", BF64.structuredMulContext BF64), ("naive", CPolynomial.MulContext.naive)] do
    let row ← runTimedSpec
      { name := s!"gs-vanishing-bf64-{label}", representation := "CPolynomial BF64",
        method := label, field := "GF(2^64)", inputShape := "32-point additive cosets",
        digestIterations := 2, digestClass := "polynomial" }
      preset
      (fun i ↦ (CPolynomial.VanishingPolynomialContext.subproduct mul).vanishingPolynomial
        (pool.getD (i % 2) #[]))
      (checksumCPolynomial fun x ↦ x.toBitVec.toNat)
      (sink := fun p ↦ p.val.foldl (fun acc x ↦ sinkStep acc (natSink x.toBitVec.toNat)) 0)
    records := records.push row
  return (⟨"gs-binary-vanishing", "Binary-field GS vanishing construction", records⟩, gen)

/-- Setup cost centers shared by the certified binary-field production decoder. -/
def binaryGSTasks : List BenchTask :=
  [BenchTask.fromGroupRunner
     ⟨"gs-interpolation-monomials", "GS weighted monomial enumeration"⟩ runMonomials,
   BenchTask.fromGroupRunner
     ⟨"gs-binary-vanishing", "Binary-field GS vanishing construction"⟩ runVanishing]

end CompPolyBench
