/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.Binary.BF64.GuruswamiSudan
public import CompPoly.Univariate.BatchEval.Interpolation

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
  for (label, V) in
      [("decoder", BF64.structuredVanishingContext BF64),
       ("naive", CPolynomial.VanishingPolynomialContext.subproduct CPolynomial.MulContext.naive)] do
    let row ← runTimedSpec
      { name := s!"gs-vanishing-bf64-{label}", representation := "CPolynomial BF64",
        method := label, field := "GF(2^64)", inputShape := "32-point additive cosets",
        digestIterations := 2, digestClass := "polynomial" }
      preset
      (fun i ↦ V.vanishingPolynomial (pool.getD (i % 2) #[]))
      (checksumCPolynomial fun x ↦ x.toBitVec.toNat)
      (sink := fun p ↦ p.val.foldl (fun acc x ↦ sinkStep acc (natSink x.toBitVec.toNat)) 0)
    records := records.push row
  return (⟨"gs-binary-vanishing", "Binary-field GS vanishing construction", records⟩, gen)

private def runWordVanishing (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (offsets, gen) := (randomNatArray 2 1000).run gen
  let pool := offsets.map fun offset ↦ (Array.range 1024).map fun i ↦
    BF64.Word.mk (UInt64.ofNat (i + 1024 * offset))
  let row ← runTimedSpec
    { name := "gs-vanishing-word", representation := "CPolynomial BF64.Word",
      method := "decoder", field := "GF(2^64)", inputShape := "1024-point additive cosets",
      digestIterations := 2, digestClass := "polynomial" }
    preset
    (fun i ↦ (BF64.structuredVanishingContext BF64.Word).vanishingPolynomial
      (pool.getD (i % 2) #[]))
    (checksumCPolynomial fun x ↦ x.val.toNat)
    (sink := fun p ↦ p.val.foldl (fun acc x ↦ sinkStep acc x.val) 0)
  return (⟨"gs-word-vanishing", "Word-field additive vanishing construction", #[row]⟩, gen)

private def runInterpolation (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (words, gen) := (randomNatArray 256 (2 ^ 64 - 3)).run gen
  let xs := (Array.range 128).map fun i ↦ BF64.ofBitVec (BitVec.ofNat 64 i)
  let pool := #[words.extract 0 128, words.extract 128 256] |>.map fun ys ↦
    ys.map fun w ↦ BF64.ofBitVec (BitVec.ofNat 64 w)
  let mut records := #[]
  for (label, interpolate) in
      [("tree", CPolynomial.interpolateSubproduct (BF64.structuredMulContext BF64)
          CPolynomial.ModContext.remainderOnly xs),
       ("coefficient", fun ys ↦ CPolynomial.interpolateCoefficientForm
          (CPolynomial.VanishingPolynomialContext.subproduct (BF64.structuredMulContext BF64))
          (CPolynomial.BatchEvalContext.subproduct BF64 (BF64.structuredMulContext BF64)
            CPolynomial.ModContext.remainderOnly) (xs.zip ys))] do
    let row ← runTimedSpec
      { name := s!"gs-interpolation-bf64-{label}", representation := "CPolynomial BF64",
        method := label, field := "GF(2^64)", inputShape := "128 additive nodes, arbitrary values",
        digestIterations := 2, digestClass := "polynomial" }
      preset (fun i ↦ interpolate (pool.getD (i % 2) #[]))
      (checksumCPolynomial fun x ↦ x.toBitVec.toNat)
      (sink := fun p ↦ p.val.foldl (fun acc x ↦ sinkStep acc (natSink x.toBitVec.toNat)) 0)
    records := records.push row
  return (⟨"gs-binary-interpolation", "Binary-field GS received interpolation", records⟩, gen)

private def runGaoEuclid (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (words, gen) := (randomNatArray 4 (2 ^ 64 - 3)).run gen
  let pool := #[words.extract 0 2, words.extract 2 4] |>.map fun xs ↦
    CPolynomial.ofArray (xs.map fun w ↦ BF64.ofBitVec (BitVec.ofNat 64 w))
  let G : CPolynomial BF64 := CPolynomial.X ^ 4
  let row ← runTimedSpec
    { name := "gao-euclid-bf64", representation := "Option CPolynomial BF64",
      method := "decoder", field := "GF(2^64)", inputShape := "k=2,n=4,degree<k",
      digestIterations := 2, digestClass := "polynomial" }
    preset (fun i ↦ ReedSolomon.Gao.decodeFrom 2 4 G (pool.getD (i % 2) 0))
    (fun p ↦ checksumCPolynomial (fun x ↦ x.toBitVec.toNat) (p.getD 0))
    (sink := fun p ↦ (p.getD 0).val.foldl
      (fun acc x ↦ sinkStep acc (natSink x.toBitVec.toNat)) 0)
  return (⟨"gs-gao-euclid", "Gao Euclidean stage and exact division", #[row]⟩, gen)

private def runBasis (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (words, gen) := (randomNatArray 8 (2 ^ 64 - 3)).run gen
  let pool := #[words.extract 0 4, words.extract 4 8] |>.map fun xs ↦
    CPolynomial.ofArray (xs.map fun w ↦ BF64.ofBitVec (BitVec.ofNat 64 w))
  let xs := (Array.range 32).map fun i ↦ BF64.ofBitVec (BitVec.ofNat 64 i)
  let G := (BF64.structuredVanishingContext BF64).vanishingPolynomial xs
  let params : GSInterpParams := ⟨4, 2, 15⟩
  let row ← runTimedSpec
    { name := "gs-basis-bf64", representation := "PolynomialMatrix BF64",
      method := "decoder", field := "GF(2^64)", inputShape := "k=4,n=32,m=2,D=15",
      digestIterations := 2, digestClass := "matrix" }
    preset (fun i ↦ leeOSullivanBasisRowsSparse (pool.getD (i % 2) 0) G params)
    (checksumArray (checksumArray (checksumCPolynomial fun x ↦ x.toBitVec.toNat)))
    (sink := fun rows ↦ rows.foldl (fun acc row ↦ row.foldl (fun acc p ↦
      p.val.foldl (fun acc x ↦ sinkStep acc (natSink x.toBitVec.toNat)) acc) acc) 0)
  return (⟨"gs-binary-basis", "Sparse vanishing powers in the GS lattice basis", #[row]⟩, gen)

private def normalizeSpec (v : Array BF64) : Option (Array BF64) :=
  match firstNonzeroIndex? v with
  | none => none
  | some i =>
    let pivot := v.getD i 0
    if pivot == 0 then none else some (v.map fun c ↦ c / pivot)

private def runNormalize (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (words, gen) := (randomNatArray 4 (2 ^ 64 - 3)).run gen
  let pool := words.map fun w ↦
    #[0, 0] ++ (Array.range 6).map fun i ↦
      if i % 3 == 0 then 0 else BF64.ofBitVec (BitVec.ofNat 64 (w + i + 2))
  let mut records := #[]
  for (label, normalize) in [("decoder", normalizeVector?), ("spec", normalizeSpec)] do
    let row ← runTimedSpec
      { name := s!"gs-normalize-bf64-{label}", representation := "Array BF64",
        method := label, field := "GF(2^64)", inputShape := "8 entries, nonzero pivot",
        digestIterations := 4, digestClass := "vector" }
      preset (fun i ↦ normalize (pool.getD (i % 4) #[]))
      (fun v ↦ checksumArray (fun x ↦ x.toBitVec.toNat) (v.getD #[]))
      (sink := fun v ↦ (v.getD #[]).foldl
        (fun acc x ↦ sinkStep acc (natSink x.toBitVec.toNat)) 0)
    records := records.push row
  return (⟨"gs-vector-normalization", "Binary-field GS vector normalization", records⟩, gen)

/-- Setup cost centers shared by the certified binary-field production decoder. -/
def binaryGSTasks : List BenchTask :=
  [BenchTask.fromGroupRunner
     ⟨"gs-word-vanishing", "Word-field additive vanishing construction"⟩ runWordVanishing,
   BenchTask.fromGroupRunner
     ⟨"gs-binary-basis", "Sparse vanishing powers in the GS lattice basis"⟩ runBasis,
   BenchTask.fromGroupRunner
     ⟨"gs-gao-euclid", "Gao Euclidean stage and exact division"⟩ runGaoEuclid,
   BenchTask.fromGroupRunner
     ⟨"gs-binary-interpolation", "Binary-field GS received interpolation"⟩ runInterpolation,
   BenchTask.fromGroupRunner
     ⟨"gs-interpolation-monomials", "GS weighted monomial enumeration"⟩ runMonomials,
   BenchTask.fromGroupRunner
     ⟨"gs-binary-vanishing", "Binary-field GS vanishing construction"⟩ runVanishing,
   BenchTask.fromGroupRunner
     ⟨"gs-vector-normalization", "Binary-field GS vector normalization"⟩ runNormalize]

end CompPolyBench
