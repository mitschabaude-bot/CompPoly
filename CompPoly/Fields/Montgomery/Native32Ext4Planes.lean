/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native32ExtPlanes

/-!
# Inverses of quartic coordinate planes

The quartic binomial extensions `Ext4 p = F[X] / (X⁴ - W)` invert their coordinate planes
(`ExtPlanes p (Ext4 p)`) as `Ext4.inv` inverts an element: `a σ(a) = g₀ + g₁ X²` for
`σ : X ↦ -X`, the norms `g₀² - W g₁²` inverted in one batch with zeros left zero, and
`a⁻¹ = σ(a) (g₀ - g₁ X²) / (g₀² - W g₁²)`. `Native32Ext4PlanesCorrectness.lean` proves it and
makes it the quartic extensions' `PlanesInv`.
-/

@[expose] public section
namespace Montgomery.Native32
open Words (addWords subWords mulWords mulAddWords invWords scaleWords)

namespace Ext4

variable {p : ℕ} [Mont32Field p] [Binomial4 p]

/-- Plane `k` of quartic planes. -/
def plane (a : ExtPlanes p (Ext4 p)) (k : Nat) : ByteArray := a.c.toArray.getD k .empty

/-- `Ext4.inv` on planes: with `σ : X ↦ -X`, `a σ(a) = g₀ + g₁ X²`, its norm `g₀² - W g₁²`
inverted in one batch, and `a⁻¹ = σ(a) (g₀ - g₁ X²) / (g₀² - W g₁²)`; zero to zero. -/
def planesInv (a : ExtPlanes p (Ext4 p)) : ExtPlanes p (Ext4 p) :=
  let B := a.n
  let W : FastField p := Binomial4.W
  let m (x y : ByteArray) := mulWords p x y B
  let ad (x y : ByteArray) := addWords p x y B
  let sb (x y : ByteArray) := subWords p x y B
  let a0 := plane a 0
  let a1 := plane a 1
  let a2 := plane a 2
  let a3 := plane a 3
  let c13 := m a1 a3
  let g0 := mulAddWords p (m a0 a0) (sb (m a2 a2) (ad c13 c13)) W.val B
  let c02 := m a0 a2
  let g1 := mulAddWords p (sb (ad c02 c02) (m a1 a1)) (m a3 a3) (-W).val B
  let ni := invWords p (mulAddWords p (m g0 g0) (m g1 g1) (-W).val B) B
  ⟨B, #v[m (mulAddWords p (m a0 g0) (m a2 g1) (-W).val B) ni,
    m (sb (scaleWords p (m a3 g1) W B) (m a1 g0)) ni,
    m (sb (m a2 g0) (m a0 g1)) ni, m (sb (m a1 g1) (m a3 g0)) ni]⟩

end Ext4

end Montgomery.Native32
