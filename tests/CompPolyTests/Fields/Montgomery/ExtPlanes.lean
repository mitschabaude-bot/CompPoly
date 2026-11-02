/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native32Ext4PlanesCorrectness
public import CompPoly.Fields.BabyBear.FastExt4
public import CompPoly.Fields.KoalaBear.FastExt4
public import CompPoly.Fields.KoalaBear.FastExt5Planes

/-! # Word kernels and coordinate planes over KoalaBear and BabyBear

The word kernels, and the plane operations of the quartic extensions of KoalaBear and BabyBear and
of KoalaBear's quintic extension, against the field and extension operations element by element,
on 1000 elements (62 blocks of sixteen words and a tail), with zeros among the inputs of the
zero-masked inversions. The packed words go through the inline C of the `ByteArray` word
accessors, so the checks run compiled, in `lake exe CompPolyNativeSmoke`.
-/

public section
namespace CompPolyTests.Fields.Montgomery.ExtPlanes

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

/-- The plane operations agree with the extension on every element. -/
def planesAgree {p : ℕ} [Mont32Field p] {E : Type} [FastExt p E] [PlanesInv p E] [BEq E]
    (a : Array (FastField p)) (x y : Array E) (s z : E) : Bool :=
  let n := a.size
  let ea := encode a
  let px : ExtPlanes p E := ExtPlanes.ofArray x
  let py : ExtPlanes p E := ExtPlanes.ofArray y
  let xz := x.mapIdx fun i e ↦ if i % 9 = 0 then 0 else e
  (px.add py).toArray == Array.zipWith (· + ·) x y &&
    (px.sub py).toArray == Array.zipWith (· - ·) x y &&
    (px.rsub s).toArray == x.map (s - ·) &&
    (px.mulBase ea).toArray == Array.zipWith (fun u v ↦ u * FastExt.ofBase v) x a &&
    (px.smul s).toArray == x.map (· * s) &&
    (px.mul py).toArray == Array.zipWith (· * ·) x y &&
    (PlanesInv.inv (ExtPlanes.ofArray xz : ExtPlanes p E)).toArray == xz.map (·⁻¹) &&
    (ExtPlanes.batchInv (ExtPlanes.ofArray xz : ExtPlanes p E)).toArray == xz.map (·⁻¹) &&
    (ExtPlanes.invDenoms z ea n : ExtPlanes p E).toArray ==
      a.map fun u ↦ (z - FastExt.ofBase u)⁻¹

/-- The word kernels agree with the field on every element. -/
def agrees (p : ℕ) [Mont32Field p] [Binomial4 p] : Bool :=
  let n := 1000
  let a := elems p n 3 0
  let b := elems p n 11 0
  let az := elems p n 5 7
  let c : FastField p := 12345
  let ea := encode a
  let eb := encode b
  addWords p ea eb n == encode (Array.zipWith (· + ·) a b) &&
    subWords p ea eb n == encode (Array.zipWith (· - ·) a b) &&
    mulWords p ea eb n == encode (Array.zipWith (· * ·) a b) &&
    mulAddWords p ea eb c.val n == encode (Array.zipWith (fun u v ↦ u + v * c) a b) &&
    replicateWord c.val n == encode (Array.replicate n c) &&
    dotAt p ea 0 eb n ==
      ((Array.zipWith (· * ·) a b).foldl (· + ·) (0 : FastField p)).val &&
    batchInvWords p ea n == encode (a.map (·⁻¹)) &&
    invWords p (encode az) n == encode (az.map (·⁻¹)) &&
    planesAgree b (exts p n 1) (exts p n 2) ⟨3, 1, 4, 1⟩ ⟨5, 6, 7, 8⟩

/-- `n` deterministic quintic elements. -/
def exts5 (n seed : ℕ) : Array KoalaBear.Fast.Ext5 :=
  Array.ofFn fun i : Fin n ↦
    ⟨((i.val + seed) ^ 3 : ℕ), ((i.val * 3 + seed) ^ 2 : ℕ), (i.val * 5 + seed : ℕ),
      ((i.val + 1) * (seed + 1) : ℕ), ((i.val + 7) * (seed + 3) ^ 2 : ℕ)⟩

/-- The quintic planes agree with `KoalaBear.Fast.Ext5`. -/
def agrees5 : Bool :=
  planesAgree (elems KoalaBear.fieldSize 1000 11 0) (exts5 1000 1) (exts5 1000 2)
    ⟨3, 1, 4, 1, 5⟩ ⟨5, 6, 7, 8, 9⟩

/-- Check KoalaBear's quartic and quintic extensions and BabyBear's quartic. -/
def run : IO Unit := do
  unless agrees KoalaBear.fieldSize do
    throw <| IO.userError "word kernels or quartic planes mismatch: KoalaBear"
  unless agrees BabyBear.fieldSize do
    throw <| IO.userError "word kernels or quartic planes mismatch: BabyBear"
  unless agrees5 do
    throw <| IO.userError "quintic planes mismatch: KoalaBear"
  IO.println "word kernels and coordinate planes: KoalaBear and BabyBear checks passed"

end CompPolyTests.Fields.Montgomery.ExtPlanes
