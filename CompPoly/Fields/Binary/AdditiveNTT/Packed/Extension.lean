/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.FlatBasis
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Layout
public import CompPoly.Fields.Binary.AdditiveNTT.ScalarExtension
public import CompPoly.Fields.Binary.BF64.WordExt3Dot

/-! # Cubic-extension encoding through consecutive packed base-field limbs -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace AdditiveNTT.Packed

open BF64 CompPoly.Extension

/-- Embed a polynomial-coordinate word as a constant extension element. -/
def extensionScalar : Word →+* Ext3 :=
  (algebraMap BF64 Ext3).comp Word.ringEquiv.toRingHom

/-- The flat basis embedded in the constant coordinate of the cubic extension. -/
def extensionBasis : Fin 64 → Ext3 := extensionScalar ∘ flatBasis

local instance : Algebra (ZMod 2) Ext3 := ZMod.algebra Ext3 2

/-- Scalar embedding preserves binary linear independence. -/
theorem extensionBasis_linearIndependent : LinearIndependent (ZMod 2) extensionBasis := by
  let φ : Word →ₐ[ZMod 2] Ext3 := {
    extensionScalar with
    commutes' := by
      intro x
      obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
      change extensionScalar ((algebraMap (ZMod 2) Word) (n : ZMod 2)) =
        (algebraMap (ZMod 2) Ext3) (n : ZMod 2)
      rw [map_natCast, map_natCast, map_natCast] }
  exact flatBasis_linearIndependent.map' φ.toLinearMap
    (LinearMap.ker_eq_bot.mpr extensionScalar.injective)

instance : Fact (LinearIndependent (ZMod 2) extensionBasis) :=
  ⟨extensionBasis_linearIndependent⟩

/-- One extension coordinate, represented by its base-field word. -/
def extensionCoordinate (c : Fin 3) (a : Ext3) : Word := Word.ofField (Ext.coeff a c)

/-- Coordinate projection is additive. -/
theorem extensionCoordinate_add (c : Fin 3) (a b : Ext3) :
    extensionCoordinate c (a + b) = extensionCoordinate c a + extensionCoordinate c b := by
  apply Word.toField_injective
  change Ext.coeff (a + b) c = Word.ringEquiv (_ + _)
  rw [Ext.coeff_add, map_add]
  rfl

/-- Base-field multiplication acts independently on each coordinate. -/
theorem extensionCoordinate_mul (c : Fin 3) (a : Word) (b : Ext3) :
    extensionCoordinate c (extensionScalar a * b) = a * extensionCoordinate c b := by
  apply Word.toField_injective
  change Ext.coeff (algebraMap BF64 Ext3 a.toField * b) c = Word.ringEquiv (_ * _)
  rw [← Algebra.smul_def, Ext.coeff_smul, map_mul]
  rfl

/-- Extension lane assembled from constant, linear and quadratic limbs in that order. -/
def extensionLaneView (a : BF64.Packed.Buffer (rows * (3 * lanes)))
    (lane : Fin lanes) : Fin rows → Ext3 := fun row =>
  Ext.ofFn fun c =>
    (laneView a ⟨3 * lane.val + c.val, by have hc : c.val < 3 := c.isLt; omega⟩ row).toField

/-- Reading an extension coordinate selects its consecutive packed limb. -/
theorem extensionCoordinate_laneView (a : BF64.Packed.Buffer (rows * (3 * lanes)))
    (lane : Fin lanes) (c : Fin 3) :
    extensionCoordinate c ∘ extensionLaneView a lane =
      laneView a ⟨3 * lane.val + c.val, by omega⟩ := by
  funext row
  simp only [extensionCoordinate, extensionLaneView, Function.comp_apply, Ext.coeff_ofFn,
    Word.ofField_toField]

/-- Packed E encoding equals the generic encoder over the cubic extension field. -/
theorem extensionLaneView_encodeRows {ell rate : Nat} (hd : ell + rate < 64)
    (p : FlatPlan (ell + rate) hd) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ ell * (3 * lanes))) (lane : Fin lanes) :
    extensionLaneView
        (forward p ell (by omega) (3 * lanes) (tileRows ell rate (3 * lanes) a)) lane =
      computableAdditiveNTT (𝔽q := ZMod 2) extensionBasis hd (extensionLaneView a lane) := by
  classical
  let : Fintype Word := Fintype.ofFinite Word
  have : Fact (LinearIndependent (ZMod 2) (extensionScalar ∘ flatBasis)) :=
    ⟨extensionBasis_linearIndependent⟩
  funext row
  apply Ext.ext
  intro c
  change Fin 3 at c
  apply Word.equivField.symm.injective
  change extensionCoordinate c
    (extensionLaneView (forward p ell (by omega) (3 * lanes)
      (tileRows ell rate (3 * lanes) a)) lane row) = extensionCoordinate c _
  have hp := congrFun (computableAdditiveNTT_project (F := ZMod 2)
    (β := flatBasis) extensionScalar (extensionCoordinate c)
    (extensionCoordinate_add c) (extensionCoordinate_mul c) hd
    (extensionLaneView a lane)) row
  change extensionCoordinate c (computableAdditiveNTT (𝔽q := ZMod 2)
    extensionBasis hd (extensionLaneView a lane) row) = _ at hp
  rw [hp]
  change (extensionCoordinate c ∘ extensionLaneView
    (forward p ell (by omega) (3 * lanes) (tileRows ell rate (3 * lanes) a)) lane) row = _
  rw [extensionCoordinate_laneView, extensionCoordinate_laneView]
  exact congrFun (laneView_encodeRows (F := ZMod 2) hd p (3 * lanes) a
    ⟨3 * lane.val + c.val, by omega⟩) row

end AdditiveNTT.Packed
