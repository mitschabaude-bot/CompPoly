/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native32Ext4Planes
public import CompPoly.Fields.BabyBear.FastExt4
public import CompPoly.Fields.KoalaBear.FastExt4

/-! # Word kernels and quartic planes over KoalaBear and BabyBear

The word kernels and the plane operations against the field and extension operations element by
element, on 1000 elements (62 blocks of sixteen words and a tail), with zeros among the inputs of
the zero-masked inversions. The packed words go through the inline C of the `ByteArray` word
accessors, so the checks run compiled, in `lake exe CompPolyNativeSmoke`.
-/

public section
namespace CompPolyTests.Fields.Montgomery.Ext4Planes

open CompPoly Montgomery.Native32 Montgomery.Native32.Words
open CompPoly.PackedRepr (encode)

/-- `n` deterministic field elements, every `zeroEvery`-th zero when `zeroEvery > 0`. -/
def elems (p : ℕ) [Mont32Field p] (n seed zeroEvery : ℕ) : Array (FastField p) :=
  Array.ofFn fun i : Fin n ↦
    if zeroEvery > 0 ∧ i.val % zeroEvery = 0 then 0 else ((i.val * 7919 + seed) ^ 3 : ℕ)

/-- `n` deterministic extension elements. -/
def exts (p : ℕ) [Mont32Field p] (n seed : ℕ) : Array (Ext4 p) :=
  Array.ofFn fun i : Fin n ↦
    ⟨((i.val + seed) ^ 3 : ℕ), ((i.val * 3 + seed) ^ 2 : ℕ), (i.val * 5 + seed : ℕ),
      ((i.val + 1) * (seed + 1) : ℕ)⟩

/-- The kernels agree with the field on every element. -/
def agrees (p : ℕ) [Mont32Field p] [Binomial4 p] : Bool :=
  let n := 1000
  let a := elems p n 3 0
  let b := elems p n 11 0
  let az := elems p n 5 7
  let c : FastField p := 12345
  let ea := encode a
  let eb := encode b
  let x := exts p n 1
  let y := exts p n 2
  let s : Ext4 p := ⟨3, 1, 4, 1⟩
  let z : Ext4 p := ⟨5, 6, 7, 8⟩
  let px := Ext4Planes.ofArray x
  let py := Ext4Planes.ofArray y
  let xz := x.mapIdx fun i e ↦ if i % 9 = 0 then 0 else e
  addWords p ea eb n == encode (Array.zipWith (· + ·) a b) &&
    subWords p ea eb n == encode (Array.zipWith (· - ·) a b) &&
    mulWords p ea eb n == encode (Array.zipWith (· * ·) a b) &&
    mulAddWords p ea eb c.val n == encode (Array.zipWith (fun u v ↦ u + v * c) a b) &&
    replicateWord c.val n == encode (Array.replicate n c) &&
    dotAt p ea 0 eb n ==
      ((Array.zipWith (· * ·) a b).foldl (· + ·) (0 : FastField p)).val &&
    batchInvWords p ea n == encode (a.map (·⁻¹)) &&
    invWords p (encode az) n == encode (az.map (·⁻¹)) &&
    (px.add py).toArray == Array.zipWith (· + ·) x y &&
    (px.sub py).toArray == Array.zipWith (· - ·) x y &&
    (px.rsub s).toArray == x.map (s - ·) &&
    (px.mulBase eb).toArray == Array.zipWith (fun u v ↦ u * Ext4.ofBase v) x b &&
    (px.smul s).toArray == x.map (· * s) &&
    (px.mul py).toArray == Array.zipWith (· * ·) x y &&
    (Ext4Planes.ofArray xz).inv.toArray == xz.map (·⁻¹) &&
    (Ext4Planes.invDenoms z ea n).toArray == a.map fun u ↦ (z - Ext4.ofBase u)⁻¹

/-- Check KoalaBear and BabyBear. -/
def run : IO Unit := do
  unless agrees KoalaBear.fieldSize do
    throw <| IO.userError "word kernels or quartic planes mismatch: KoalaBear"
  unless agrees BabyBear.fieldSize do
    throw <| IO.userError "word kernels or quartic planes mismatch: BabyBear"
  IO.println "word kernels and quartic planes: KoalaBear and BabyBear checks passed"

end CompPolyTests.Fields.Montgomery.Ext4Planes
