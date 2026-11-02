/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native32Words
public import CompPoly.Fields.Montgomery.InterpolateCosetPacked

/-!
# Vectors of quartic extension elements as coordinate planes

`Ext4Planes p` holds `n` elements of `Ext4 p = F[X] / (X⁴ - W)` as four planes of packed
Montgomery words, one per coordinate, so that every operation is a few vectorized passes of the
word kernels (`Native32Words.lean`) over base-field words and allocates no extension element.

* Products reduce by `X⁴ = W` coordinate by coordinate (`mul`, `smul`).
* `inv` follows `Ext4.inv`: `a σ(a) = g₀ + g₁ X²` for `σ : X ↦ -X`, the norms `g₀² - W g₁²`
  inverted in one batch with zeros left zero, and `a⁻¹ = σ(a) (g₀ - g₁ X²) / (g₀² - W g₁²)`.
* `invDenoms z xs` gives `1 / (z - x)` for base points `x` without extension inversions: with
  `t = z₀ - x`, `1 / (z - x) = (b₀ + t b₁ + t² b₂ + t³) / N(t)` for extension constants `bₖ` of
  `z` (`Ext4.adj0`, `Ext4.adj1`, `Ext4.adj2`) and the norm `N(t)` of `z - x`, a quartic in `t`
  with base coefficients (`Ext4.normAt`), so a point costs base-field products and one shared
  base-field batch inversion.

`Native32Ext4PlanesCorrectness.lean` proves every operation equal to the extension's on the
represented arrays (`Ext4Planes.Rel`).
-/

@[expose] public section
namespace Montgomery.Native32
open CompPoly.CPolynomial.NTTFast.Packed (ofWord)
open CompPoly.CPolynomial.NTTFast.Packed.Native (read zeroWords encodeFields)
open Words (addWords subWords mulWords mulAddWords replicateWord batchInvWords invWords
  scaleWords)

/-- `n` elements of `Ext4 p` as four coordinate planes of words. -/
structure Ext4Planes (p : ℕ) where
  n : Nat
  c0 : ByteArray
  c1 : ByteArray
  c2 : ByteArray
  c3 : ByteArray

namespace Ext4Planes

variable {p : ℕ} [Mont32Field p]

/-- Element `i`. -/
def get (v : Ext4Planes p) (i : Nat) : Ext4 p :=
  ⟨ofWord p (read v.c0 i), ofWord p (read v.c1 i), ofWord p (read v.c2 i),
    ofWord p (read v.c3 i)⟩

/-- The planes of an array. -/
def ofArray (xs : Array (Ext4 p)) : Ext4Planes p :=
  ⟨xs.size, encodeFields (xs.map (·.c0)), encodeFields (xs.map (·.c1)),
    encodeFields (xs.map (·.c2)), encodeFields (xs.map (·.c3))⟩

/-- The elements. -/
def toArray (v : Ext4Planes p) : Array (Ext4 p) := Array.ofFn (n := v.n) fun i ↦ v.get i

/-- Zeros. -/
def zeros (n : Nat) : Ext4Planes p := ⟨n, zeroWords n, zeroWords n, zeroWords n, zeroWords n⟩

def add (a b : Ext4Planes p) : Ext4Planes p :=
  ⟨a.n, addWords p a.c0 b.c0 a.n, addWords p a.c1 b.c1 a.n, addWords p a.c2 b.c2 a.n,
    addWords p a.c3 b.c3 a.n⟩

def sub (a b : Ext4Planes p) : Ext4Planes p :=
  ⟨a.n, subWords p a.c0 b.c0 a.n, subWords p a.c1 b.c1 a.n, subWords p a.c2 b.c2 a.n,
    subWords p a.c3 b.c3 a.n⟩

/-- `s - a` for an extension scalar `s`. -/
def rsub (s : Ext4 p) (a : Ext4Planes p) : Ext4Planes p :=
  ⟨a.n, subWords p (replicateWord s.c0.val a.n) a.c0 a.n,
    subWords p (replicateWord s.c1.val a.n) a.c1 a.n,
    subWords p (replicateWord s.c2.val a.n) a.c2 a.n,
    subWords p (replicateWord s.c3.val a.n) a.c3 a.n⟩

/-- Every element times a base vector `b`. -/
def mulBase (a : Ext4Planes p) (b : ByteArray) : Ext4Planes p :=
  ⟨a.n, mulWords p a.c0 b a.n, mulWords p a.c1 b a.n, mulWords p a.c2 b a.n,
    mulWords p a.c3 b a.n⟩

/-- `∑ⱼ planes[j] · s[j]` for scalar words `s`. -/
def combine (p : ℕ) [Mont32Field p] (n : Nat) (terms : List (ByteArray × UInt32)) : ByteArray :=
  terms.foldl (fun acc (x, s) ↦ mulAddWords p acc x s n) (zeroWords n)

/-- Concatenate the planes of parallel pieces, each piece its four planes. -/
def join (p : ℕ) (n : Nat) (pieces : Array (Task (Array ByteArray))) : Ext4Planes p :=
  let cat (j : Nat) := pieces.foldl (fun acc t ↦ acc ++ t.get.getD j .empty)
    (ByteArray.emptyWithCapacity (4 * n))
  ⟨n, cat 0, cat 1, cat 2, cat 3⟩

variable [Binomial4 p]

/-- Every element times an extension scalar `s`: with `X⁴ = W`,
`(a s)₀ = a₀s₀ + W (a₁s₃ + a₂s₂ + a₃s₁)` and so on. -/
def smul (a : Ext4Planes p) (s : Ext4 p) : Ext4Planes p :=
  let t (x : FastField p) : UInt32 := (Binomial4.mulW x).val
  ⟨a.n, combine p a.n [(a.c0, s.c0.val), (a.c1, t s.c3), (a.c2, t s.c2), (a.c3, t s.c1)],
    combine p a.n [(a.c0, s.c1.val), (a.c1, s.c0.val), (a.c2, t s.c3), (a.c3, t s.c2)],
    combine p a.n [(a.c0, s.c2.val), (a.c1, s.c1.val), (a.c2, s.c0.val), (a.c3, t s.c3)],
    combine p a.n [(a.c0, s.c3.val), (a.c1, s.c2.val), (a.c2, s.c1.val), (a.c3, s.c0.val)]⟩

/-- Elementwise products: with `X⁴ = W`, `(a b)₀ = a₀b₀ + (a₁b₃ + a₂b₂ + a₃b₁) W` and so on, the
multiple of `W` a multiply-add. -/
def mul (a b : Ext4Planes p) : Ext4Planes p :=
  let n := a.n
  let w := (Binomial4.W (p := p)).val
  let m (x y : ByteArray) := mulWords p x y n
  let s (xs : List ByteArray) := xs.foldl (fun acc x ↦ addWords p acc x n) (zeroWords n)
  ⟨n, mulAddWords p (m a.c0 b.c0) (s [m a.c1 b.c3, m a.c2 b.c2, m a.c3 b.c1]) w n,
    mulAddWords p (s [m a.c0 b.c1, m a.c1 b.c0]) (s [m a.c2 b.c3, m a.c3 b.c2]) w n,
    mulAddWords p (s [m a.c0 b.c2, m a.c1 b.c1, m a.c2 b.c0]) (m a.c3 b.c3) w n,
    s [m a.c0 b.c3, m a.c1 b.c2, m a.c2 b.c1, m a.c3 b.c0]⟩

/-- `Ext4.inv` on planes: with `σ : X ↦ -X`, `a σ(a) = g₀ + g₁ X²`, its norm `g₀² - W g₁²`
inverted in one batch, and `a⁻¹ = σ(a) (g₀ - g₁ X²) / (g₀² - W g₁²)`; zero to zero. -/
def inv (a : Ext4Planes p) : Ext4Planes p :=
  let B := a.n
  let W : FastField p := Binomial4.W
  let m (x y : ByteArray) := mulWords p x y B
  let ad (x y : ByteArray) := addWords p x y B
  let sb (x y : ByteArray) := subWords p x y B
  let c13 := m a.c1 a.c3
  let g0 := mulAddWords p (m a.c0 a.c0) (sb (m a.c2 a.c2) (ad c13 c13)) W.val B
  let c02 := m a.c0 a.c2
  let g1 := mulAddWords p (sb (ad c02 c02) (m a.c1 a.c1)) (m a.c3 a.c3) (-W).val B
  let ni := invWords p (mulAddWords p (m g0 g0) (m g1 g1) (-W).val B) B
  ⟨B, m (mulAddWords p (m a.c0 g0) (m a.c2 g1) (-W).val B) ni,
    m (sb (scaleWords p (m a.c3 g1) W B) (m a.c1 g0)) ni,
    m (sb (m a.c2 g0) (m a.c0 g1)) ni, m (sb (m a.c1 g1) (m a.c3 g0)) ni⟩

/-- `1 / (z - x)` for the `n` base points `xs`, by the norm (see the module docs). -/
def invDenoms (z : Ext4 p) (xs : ByteArray) (n : Nat) : Ext4Planes p :=
  let rep (c : FastField p) := replicateWord c.val n
  let t := subWords p (rep z.c0) xs n
  let t2 := mulWords p t t n
  let g0 := addWords p t2 (rep (Ext4.normK0 z)) n
  let g1 := mulAddWords p (rep (Ext4.normK1 z)) t (z.c2 + z.c2).val n
  let invN := batchInvWords p
    (mulAddWords p (mulWords p g0 g0 n) (mulWords p g1 g1 n) (-Binomial4.W (p := p)).val n) n
  let q (c : Ext4 p → FastField p) : ByteArray :=
    mulAddWords p (mulAddWords p (rep (c (Ext4.adj0 z))) t (c (Ext4.adj1 z)).val n) t2
      (c (Ext4.adj2 z)).val n
  ⟨n, mulWords p (addWords p (q (·.c0)) (mulWords p t2 t n) n) invN n,
    mulWords p (q (·.c1)) invN n, mulWords p (q (·.c2)) invN n, mulWords p (q (·.c3)) invN n⟩

end Ext4Planes

end Montgomery.Native32
