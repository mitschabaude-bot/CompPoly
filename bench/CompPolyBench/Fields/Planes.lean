/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.KoalaBear.FastExt4
public import CompPoly.Fields.KoalaBear.FastExt5Planes
public import CompPoly.Fields.Montgomery.Native32Ext4PlanesCorrectness

/-!
# Coordinate-plane benchmarks

Times the operations of vectors of extension elements as coordinate planes (`ExtPlanes`) over
KoalaBear's quartic and quintic extensions, on 4096 elements: elementwise products, products by an
extension scalar, inverses, and the inverses of `z - x` over base points. Each group has one
record; its digest is the checksum of the last output plane, so an A/B comparison also checks that
both builds compute the same planes.
-/

public section

open CompPoly Montgomery.Native32
open CompPoly.CPolynomial.NTTFast.Packed.Native (read encodeFields)

namespace CompPolyBench

/-- The number of elements of a vector. -/
private def planesSize : Nat := 4096

/-- Sum of the words of a plane. -/
private def planeChecksum (b : ByteArray) : Nat :=
  (List.range (b.size / 4)).foldl (fun acc i ↦ acc + (read b i).toNat) 0

/-- The inputs: two vectors, base points, and two scalars, from KoalaBear values. -/
private structure PlanesInputs (E : Type) where
  xs : Array E
  ys : Array E
  pts : Array KoalaBear.Fast.Field
  s : E
  z : E

/-- Inputs for an extension of degree `d` from `ofCoords`. -/
private def planesInputs {E : Type} (d : Nat) (mk : (Nat → KoalaBear.Fast.Field) → E)
    (gen : StdGen) : PlanesInputs E × StdGen :=
  let (values, gen) := (koalaBearArray ((2 * planesSize + 3) * d + planesSize) false).run gen
  let fv := koalaBearFastArray values
  let elem (o : Nat) : E := mk fun k ↦ fv.getD (o + k) 0
  ({ xs := Array.ofFn (n := planesSize) fun i ↦ elem (d * i.val)
     ys := Array.ofFn (n := planesSize) fun i ↦ elem (d * (planesSize + i.val))
     pts := Array.ofFn (n := planesSize) fun i ↦ fv.getD ((2 * planesSize + 2) * d + i.val) 0
     s := elem (2 * planesSize * d)
     z := elem ((2 * planesSize + 1) * d) }, gen)

/-- One plane operation as a single-record group, its inputs prepared outside timing; the result
is its last plane. -/
private def runPlanesOp (groupKey title name method fieldName : String)
    (mkOp : IO (Nat → ByteArray)) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let op ← mkOp
  let record ← runTimedSpec
    { name := name, representation := "ExtPlanes", method := method, field := fieldName,
      inputShape := s!"{planesSize} elements", digestIterations := 2 }
    preset op planeChecksum (sink := fun b ↦ (read b 0).toUInt64)
  pure ({ groupKey := groupKey, title := title, records := #[record] }, gen)

/-- The four plane groups of an extension. -/
@[specialize] private def planesTasksFor {p : ℕ} [Mont32Field p] {E : Type} [FastExt p E]
    [PlanesInv p E] (key fieldName : String) (d : Nat) (mk : (Nat → KoalaBear.Fast.Field) → E)
    (last : ExtPlanes p E → ByteArray)
    (base : Array KoalaBear.Fast.Field → ByteArray) : List BenchTask :=
  let inputs (gen : StdGen) := planesInputs d mk gen
  let task (op title method : String) (f : PlanesInputs E → IO (Nat → ByteArray)) : BenchTask :=
    BenchTask.fromGroupRunner ⟨s!"fields-planes-{key}-{op}", title⟩ fun preset gen ↦
      let (inp, gen) := inputs gen
      runPlanesOp s!"fields-planes-{key}-{op}" title s!"planes-{op}" method fieldName
        (f inp) preset gen
  [task "mul" s!"Elementwise products of planes ({fieldName})" "mul" fun inp ↦ do
      let a : ExtPlanes p E ← IO.lazyPure fun _ ↦ ExtPlanes.ofArray inp.xs
      let b : ExtPlanes p E ← IO.lazyPure fun _ ↦ ExtPlanes.ofArray inp.ys
      pure fun i ↦ last (if i % 2 = 0 then a.mul b else b.mul a),
    task "smul" s!"Products of planes by a scalar ({fieldName})" "smul" fun inp ↦ do
      let a : ExtPlanes p E ← IO.lazyPure fun _ ↦ ExtPlanes.ofArray inp.xs
      let b : ExtPlanes p E ← IO.lazyPure fun _ ↦ ExtPlanes.ofArray inp.ys
      pure fun i ↦ last ((if i % 2 = 0 then a else b).smul inp.s),
    task "inv" s!"Inverses of planes ({fieldName})" "PlanesInv.inv" fun inp ↦ do
      let a : ExtPlanes p E ← IO.lazyPure fun _ ↦ ExtPlanes.ofArray inp.xs
      let b : ExtPlanes p E ← IO.lazyPure fun _ ↦ ExtPlanes.ofArray inp.ys
      pure fun i ↦ last (PlanesInv.inv (if i % 2 = 0 then a else b)),
    task "invdenoms" s!"Inverses of z - x over base points ({fieldName})" "invDenoms" fun inp ↦ do
      let xs ← IO.lazyPure fun _ ↦ base inp.pts
      pure fun i ↦ last (ExtPlanes.invDenoms (if i % 2 = 0 then inp.z else inp.s) xs planesSize)]

/-- Registry entries for the coordinate-plane benchmarks. -/
def planesTasks : List BenchTask :=
  planesTasksFor (E := KoalaBear.Fast.Ext4) "koalabear-ext4" "KoalaBear.Fast.Ext4" 4
      (fun f ↦ ⟨f 0, f 1, f 2, f 3⟩) (fun v ↦ v.c.toArray.getD 3 .empty) encodeFields ++
    planesTasksFor (E := KoalaBear.Fast.Ext5) "koalabear-ext5" "KoalaBear.Fast.Ext5" 5
      (fun f ↦ ⟨f 0, f 1, f 2, f 3, f 4⟩) (fun v ↦ v.c.toArray.getD 4 .empty) encodeFields

end CompPolyBench
