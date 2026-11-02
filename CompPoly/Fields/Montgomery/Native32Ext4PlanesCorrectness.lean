/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native32Ext4Planes
public import CompPoly.Fields.Montgomery.Native32ExtPlanesCorrectness

/-!
# Inverses of quartic coordinate planes

The coordinates of products in `Ext4 p` (`Ext4.mul_coords`), and the norm inversion of quartic
planes, `Ext4.planesInv`, as `Ext4.inv` coordinate by coordinate with zero to zero
(`Ext4.planesInv_rel`): the quartic extensions' `PlanesInv`.
-/

@[expose] public section

namespace Montgomery.Native32.Ext4

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p
local notation "W" => (Binomial4.W : FastField p)

theorem mul_c0 [Binomial4 p] (a b : EF) :
    (a * b).c0 = a.c0 * b.c0 + W * (a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1) := by
  show (Ext4.mul a b).c0 = _
  simp only [Ext4.mul, mulAdd4_eq, Binomial4.mulW_eq]; ring

theorem mul_c1 [Binomial4 p] (a b : EF) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + W * (a.c2 * b.c3 + a.c3 * b.c2) := by
  show (Ext4.mul a b).c1 = _
  simp only [Ext4.mul, mulAdd4_eq, Binomial4.mulW_eq]; ring

theorem mul_c2 [Binomial4 p] (a b : EF) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + W * (a.c3 * b.c3) := by
  show (Ext4.mul a b).c2 = _
  simp only [Ext4.mul, mulAdd4_eq, Binomial4.mulW_eq]; ring

theorem mul_c3 [Binomial4 p] (a b : EF) :
    (a * b).c3 = a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0 := by
  show (Ext4.mul a b).c3 = _
  simp only [Ext4.mul, mulAdd4_eq]

theorem toSpec_ne_zero [Binomial4 p] {a : EF} (h : a ≠ 0) : Ext4.toSpec a ≠ 0 := fun h' ↦
  h (Ext4.toSpec_injective (h'.trans Ext4.toSpec_zero.symm))

theorem smul_eq_ofBase_mul [Binomial4 p] (x : F) (a : EF) :
    Ext4.smul x a = Ext4.ofBase x * a := by
  apply ext' <;> simp only [Ext4.smul, Ext4.ofBase, mul_c0, mul_c1, mul_c2, mul_c3] <;> ring

/-- The coordinates of the products in `F[X] / (X⁴ - W)`. -/
theorem mul_coords [Binomial4 p] (x y : EF) : x * y =
    ⟨x.c0 * y.c0 + W * (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1),
      x.c0 * y.c1 + x.c1 * y.c0 + W * (x.c2 * y.c3 + x.c3 * y.c2),
      x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 + W * (x.c3 * y.c3),
      x.c0 * y.c3 + x.c1 * y.c2 + x.c2 * y.c1 + x.c3 * y.c0⟩ := by
  apply ext' <;>
    simp only [show x * y = Montgomery.Native32.Ext4.mul x y from rfl, Montgomery.Native32.Ext4.mul,
      Binomial4.mulW_eq, mulAdd4_eq] <;> ring

theorem mul_ofBase [Binomial4 p] (a : EF) (x : F) : a * Ext4.ofBase x = Ext4.smul x a := by
  apply ext' <;>
    simp only [mul_c0, mul_c1, mul_c2, mul_c3, Ext4.ofBase, Ext4.smul] <;>
    ring

theorem mul_comm' [Binomial4 p] (a b : EF) : a * b = b * a := by
  rw [Ext4.mul_coords, Ext4.mul_coords]
  congr 1 <;> ring

theorem add_zero' (a : EF) : a + 0 = a := by
  show (⟨a.c0 + 0, a.c1 + 0, a.c2 + 0, a.c3 + 0⟩ : EF) = a
  simp only [add_zero]

theorem mul_ofBase_zero [Binomial4 p] (a : EF) : a * Ext4.ofBase 0 = 0 := by
  rw [Ext4.mul_coords]
  simp only [ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3, MulZeroClass.mul_zero, add_zero]
  rfl
/-! ### Inverses of planes -/

open CompPoly.PackedRepr (encode)
open Words

theorem plane_eq [Binomial4 p] {B : Nat} {v : ExtPlanes p EF} {f : Nat → EF}
    (hv : ExtPlanes.Rel v (tab B f))
    (k : Nat) (hk : k < 4) : plane v k = encode (tab B fun i ↦ coord (f i) k) := by
  rw [plane, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp; exact hk),
    Option.getD_some, Vector.getElem_toArray]
  exact (ExtPlanes.rel_tab_iff.mp hv).2 ⟨k, hk⟩

/-- **Inverses of quartic planes**: `Ext4.inv` coordinate by coordinate, zero to zero. -/
theorem planesInv_rel [Binomial4 p] {B : Nat} (hB : 4 * B < USize.size) {v : ExtPlanes p EF}
    {f : Nat → EF} (hv : ExtPlanes.Rel v (tab B f)) :
    ExtPlanes.Rel (planesInv v) (tab B fun i ↦ (f i)⁻¹) := by
  have hn := (ExtPlanes.rel_tab_iff.mp hv).1
  unfold planesInv
  simp only [hn, plane_eq hv 0 (by decide), plane_eq hv 1 (by decide), plane_eq hv 2 (by decide),
    plane_eq hv 3 (by decide), mulWords_tab hB, addWords_tab hB, subWords_tab hB,
    mulAddWords_tab hB, scaleWords_tab hB, invWords_tab hB]
  refine ExtPlanes.rel_mk _ _ fun ⟨k, hk⟩ ↦ ?_
  have hk : k < 4 := hk
  interval_cases k <;>
  · refine congrArg encode (tab_congr fun i _ ↦ ?_)
    first
      | show _ = (Ext4.inv (f i)).c0
      | show _ = (Ext4.inv (f i)).c1
      | show _ = (Ext4.inv (f i)).c2
      | show _ = (Ext4.inv (f i)).c3
    simp only [Ext4.inv, Ext4.g0, Ext4.g1, Ext4.norm, Binomial4.mulW_eq, coord]
    ring

/-- The quartic extensions invert planes by their norm. -/
instance instPlanesInv [Binomial4 p] : PlanesInv p (Ext4 p) where
  inv := planesInv
  inv_rel {v a} hv hs := by
    rw [ExtPlanes.tab_getD a] at hv
    refine (planesInv_rel hs hv).congr ?_
    rw [ExtPlanes.tab_getD (a.map (·⁻¹)), Array.size_map]
    refine tab_congr fun i hi ↦ ?_
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some]

end Montgomery.Native32.Ext4
