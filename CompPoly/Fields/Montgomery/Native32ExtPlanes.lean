/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.FastExt
public import CompPoly.Fields.Montgomery.Native32Words
public import CompPoly.Fields.Montgomery.InterpolateCosetPacked
public import CompPoly.Data.Array.BatchInv

/-!
# Vectors of extension elements as coordinate planes

`ExtPlanes p E` holds `n` elements of a fast extension `E` of `FastField p` (`FastExt p E`, of
degree `d`) as `d` planes of packed Montgomery words, one per coordinate, so that every operation
is a few vectorized passes of the word kernels (`Native32Words.lean`) over base-field words and
allocates no extension element. Every operation is generic over the modulus and the degree.

* Products by an extension scalar `s` (`smul`) are, coordinate by coordinate, combinations of the
  planes with the coordinates of `Xⁱ s` as scalars.
* Products (`mul`) follow the spec's `Ext.mulTbl`: the `2d - 1` coefficient planes of the
  unreduced product, then coordinate `m` the plane `m` plus the higher planes `k` times
  `[Xᵏ mod f]ₘ`, a multiply-add per nonzero entry, an addition or subtraction for `±1`.
* `invDenoms z xs` gives `1 / (z - x)` for base points `x`: with the product
  `adj(Y) = ∏_{1 ≤ j < d} (φʲ(z) - Y)` of the other conjugates of `z` (`φ` the Frobenius
  `y ↦ y^p`) and the norm polynomial `N(Y) = (z - Y) adj(Y)`, whose values at base points lie in
  the base field, `1 / (z - x) = adj(x) / N(x)`, so a point costs base-field products and one
  shared base-field batch inversion.
* Inverses are the extension's choice (`PlanesInv`): `batchInv` is Montgomery's batch inversion
  of the elements, for any extension; the quartic binomial extensions invert by their norm
  (`Native32Ext4Planes.lean`).

`Native32ExtPlanesCorrectness.lean` proves every operation equal to the extension's on the
represented arrays (`ExtPlanes.Rel`).
-/

@[expose] public section
namespace Montgomery.Native32
open CompPoly.Extension
open CompPoly.CPolynomial.NTTFast.Packed (ofWord)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read zeroWords encodeFields)
open Words (addWords subWords mulWords mulAddWords mulAdd4Into replicateWord batchInvWords invWords)

/-- `n` elements of the fast extension `E` as `d` coordinate planes of words. -/
structure ExtPlanes (p : ℕ) [Mont32Field p] (E : Type) [FastExt p E] where
  n : Nat
  c : Vector ByteArray (FastExt.d p E)

namespace FastExt

variable {p : ℕ} [Mont32Field p] {E : Type} [FastExt p E]

/-- `a ^ n` by repeated squaring. -/
def pow (a : E) (n : ℕ) : E := npowBinRec n a

/-- The Frobenius power `a ^ (p ^ e)`. -/
def frobE (e : Nat) (a : E) : E := pow a (p ^ e)

end FastExt

namespace ExtPlanes

variable {p : ℕ} [Mont32Field p] {E : Type} [FastExt p E]

local notation "d" => FastExt.d p E

/-- Element `i`. -/
def get (v : ExtPlanes p E) (i : Nat) : E :=
  FastExt.ofCoords fun k ↦ ofWord p (read v.c[k] i)

/-- The planes of an array. -/
def ofArray (xs : Array E) : ExtPlanes p E :=
  ⟨xs.size, Vector.ofFn fun k ↦ encodeFields (xs.map (FastExt.coord · k))⟩

/-- The elements. -/
def toArray (v : ExtPlanes p E) : Array E := Array.ofFn (n := v.n) fun i ↦ v.get i

/-- Zeros. -/
def zeros (n : Nat) : ExtPlanes p E := ⟨n, Vector.replicate d (zeroWords n)⟩

def add (a b : ExtPlanes p E) : ExtPlanes p E :=
  ⟨a.n, Vector.ofFn fun k ↦ addWords p a.c[k] b.c[k] a.n⟩

def sub (a b : ExtPlanes p E) : ExtPlanes p E :=
  ⟨a.n, Vector.ofFn fun k ↦ subWords p a.c[k] b.c[k] a.n⟩

/-- `s - a` for an extension scalar `s`. -/
def rsub (s : E) (a : ExtPlanes p E) : ExtPlanes p E :=
  ⟨a.n, Vector.ofFn fun k ↦ subWords p (replicateWord (FastExt.coord s k).val a.n) a.c[k] a.n⟩

/-- Every element times a base vector `b`. -/
def mulBase (a : ExtPlanes p E) (b : ByteArray) : ExtPlanes p E :=
  ⟨a.n, Vector.ofFn fun k ↦ mulWords p a.c[k] b a.n⟩

/-- `∑_{i < k} planes i · s i`: four planes multiply-added at a time, every word reduced once
per four planes (`Words.mulAdd4Into`); the planes past `k` are ones of the right size with zero
scalars. -/
def combine (p : ℕ) [Mont32Field p] (n k : Nat) (planes : Nat → ByteArray)
    (s : Nat → FastField p) : ByteArray :=
  (List.range ((k + 3) / 4)).foldl (fun acc g ↦
    mulAdd4Into p acc (planes (4 * g)) (planes (4 * g + 1)) (planes (4 * g + 2))
      (planes (4 * g + 3)) 0 0 0 0 (s (4 * g)).val (s (4 * g + 1)).val (s (4 * g + 2)).val
      (s (4 * g + 3)).val n) (zeroWords n)

/-- Concatenate the planes of parallel pieces, each piece its `d` planes. -/
def join (n : Nat) (pieces : Array (Task (Array ByteArray))) : ExtPlanes p E :=
  ⟨n, Vector.ofFn fun k ↦ pieces.foldl (fun acc t ↦ acc ++ t.get.getD k .empty)
    (ByteArray.emptyWithCapacity (4 * n))⟩

/-- Every element times an extension scalar `s`: coordinate `m` is `∑ᵢ aᵢ [Xⁱ s]ₘ`, the planes
multiply-added four at a time (`combine`). -/
def smul (a : ExtPlanes p E) (s : E) : ExtPlanes p E :=
  let cols : Vector E d := Vector.ofFn fun i ↦ FastExt.pow FastExt.gen (i : ℕ) * s
  ⟨a.n, Vector.ofFn fun m ↦ combine p a.n d
    (fun i ↦ if h : i < d then a.c[i] else a.c[0]'(FastExt.params (p := p) (E := E)).d_pos)
    fun i ↦ if h : i < d then FastExt.coord cols[i] m else 0⟩

/-- The sum of planes, the first one if any. -/
def sumWords (p : ℕ) [Mont32Field p] (n : Nat) : List ByteArray → ByteArray
  | [] => zeroWords n
  | x :: xs => xs.foldl (fun acc y ↦ addWords p acc y n) x

/-- Plane `k` of the unreduced product: `∑_{i + j = k} aᵢ bⱼ`. -/
def convPlane (a b : ExtPlanes p E) (k : Nat) : ByteArray :=
  sumWords p a.n ((List.finRange d).filterMap fun (i : Fin d) ↦
    if h : (i : ℕ) ≤ k ∧ k - (i : ℕ) < d then
      some (mulWords p a.c[i] (b.c[k - (i : ℕ)]'h.2) a.n)
    else none)

/-- `acc + x · s` for a field scalar `s`: an addition or a subtraction for `±1`. -/
def addScaled (p : ℕ) [Mont32Field p] (n : Nat) (acc x : ByteArray) (s : FastField p) :
    ByteArray :=
  if s = 1 then addWords p acc x n
  else if s = -1 then subWords p acc x n
  else mulAddWords p acc x s.val n

/-- Coordinate `m` of the reduction of the planes `conv k` of an unreduced product against the
table `tbl` of `Xᵏ mod f` (`Ext.red`): plane `m` plus the planes `k ≥ d` times `[Xᵏ mod f]ₘ`, the
zero entries skipped. -/
def reduceCoord (tbl : Array (FastExt.Spec p E)) (conv : Nat → ByteArray) (n : Nat) (m : Fin d) :
    ByteArray :=
  (List.range' d (d - 1)).foldl (fun acc k ↦
    let s := Ext.coeff (tbl.getD k 0) m
    if s = 0 then acc else addScaled p n acc (conv k) s) (conv m)

/-- Elementwise products, as `Ext.mulTbl`: the planes of the unreduced product, reduced. -/
def mul (a b : ExtPlanes p E) : ExtPlanes p E :=
  let tbl := (Ext.red (FastExt.params (p := p) (E := E))).toArray
  let conv := Array.ofFn (n := 2 * d - 1) fun k ↦ convPlane a b k
  ⟨a.n, Vector.ofFn fun m ↦ reduceCoord tbl (fun k ↦ conv.getD k .empty) a.n m⟩

/-- Inverses, zero to zero, by Montgomery's batch inversion of the elements: zeros replaced by
one, then masked. -/
def batchInv (a : ExtPlanes p E) : ExtPlanes p E :=
  let xs := a.toArray
  let inv := CompPoly.Array.batchInv (xs.map fun x ↦ if x = 0 then 1 else x)
  ofArray (Array.zipWith (fun x y ↦ if x = 0 then 0 else y) xs inv)

/-- The coefficients of `(w - Y) · ∑ₖ csₖ Yᵏ`. -/
def mulLinear (cs : List E) (w : E) : List E :=
  (List.range (cs.length + 1)).map fun k ↦
    w * cs.getD k 0 - if k = 0 then 0 else cs.getD (k - 1) 0

/-- The coefficients of `∏_{1 ≤ j < d} (φʲ(z) - Y)`. -/
def adjCoeffs (z : E) : List E :=
  (List.range (d - 1)).foldl (fun cs j ↦ mulLinear cs (FastExt.frobE (j + 1) z)) [1]

/-- Coordinate `m` of `∑ₖ csₖ xᵏ` on the planes `xpow k = x^(k + 1)`. -/
def evalCoord (cs : List E) (m : Fin d) (n : Nat) (xpow : Nat → ByteArray) : ByteArray :=
  (List.range (cs.length - 1)).foldl (fun acc k ↦
    let s := FastExt.coord (cs.getD (k + 1) 0) m
    if s = 0 then acc else mulAddWords p acc (xpow k) s.val n)
    (replicateWord (FastExt.coord (cs.getD 0 0) m).val n)

/-- The planes `x, x², …, xᵈ`. -/
def powerPlanes (p : ℕ) [Mont32Field p] (xs : ByteArray) (n k : Nat) : Array ByteArray :=
  (List.range k).foldl (fun acc _ ↦ acc.push (mulWords p (acc.getD (acc.size - 1) .empty) xs n))
    #[xs]

/-- `1 / (z - x)` for the `n` base points `xs`, by the norm polynomial (see the module docs). -/
def invDenoms (z : E) (xs : ByteArray) (n : Nat) : ExtPlanes p E :=
  let adj := adjCoeffs z
  let pows := powerPlanes p xs n (d - 1)
  let xpow (k : Nat) := pows.getD k .empty
  let invN := batchInvWords p
    (evalCoord (mulLinear adj z) ⟨0, ExtensionParams.d_pos _⟩ n xpow) n
  ⟨n, Vector.ofFn fun m ↦ mulWords p (evalCoord adj m n xpow) invN n⟩

/-- Planes represent the elements whose coordinates they encode. -/
def Rel (v : ExtPlanes p E) (a : Array E) : Prop :=
  v.n = a.size ∧ ∀ k : Fin d, v.c[k] = CompPoly.PackedRepr.encode (a.map (FastExt.coord · k))

end ExtPlanes

/-- An inversion of coordinate planes, zero to zero: the extension's choice of kernel. -/
class PlanesInv (p : outParam ℕ) [Mont32Field p] (E : Type) [FastExt p E] where
  inv : ExtPlanes p E → ExtPlanes p E
  inv_rel {v : ExtPlanes p E} {a : Array E} (hv : ExtPlanes.Rel v a)
    (hs : 4 * a.size < USize.size) : ExtPlanes.Rel (inv v) (a.map (·⁻¹))

end Montgomery.Native32
