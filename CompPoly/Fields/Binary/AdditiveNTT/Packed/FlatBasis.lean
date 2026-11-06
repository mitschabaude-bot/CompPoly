/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Plan
public import CompPoly.Fields.Binary.BF64.Trace

/-! # Independence of the flat polynomial-coordinate basis on word carriers -/

@[expose] public section

namespace AdditiveNTT.Packed

open BF64

instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨by decide⟩

instance : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨by rw [ZMod.ringChar_zmod_n]; decide⟩

instance : CharP Word 2 := Word.ringEquiv.toRingHom.charP Word.ringEquiv.injective 2

instance : Algebra (ZMod 2) Word := ZMod.algebra Word 2

instance : Finite Word := Finite.of_equiv BF64 Word.equivField.symm

local instance : Algebra (ZMod 2) BF64 := ZMod.algebra BF64 2

/-- The word/specification ring equivalence respects binary scalars. -/
def wordBinaryAlgEquiv : Word ≃ₐ[ZMod 2] BF64 := by
  exact AlgEquiv.ofRingEquiv (f := Word.ringEquiv) (by
    intro x
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
    simp only [map_natCast])

/-- The flat machine-word basis has the specification field's polynomial coordinates. -/
theorem flatBasis_toField (i : Fin 64) :
    (flatBasis i).toField = binaryBasisVector i := by
  apply BF64.ext
  change ((1 : UInt64) <<< UInt64.ofNat i.val).toBitVec = (1 : BitVec 64) <<< i.val
  rw [UInt64.toBitVec_shiftLeft]
  simp only [UInt64.toBitVec_ofNat, UInt64.toBitVec_ofNat', BitVec.shiftLeft_eq',
    BitVec.toNat_umod, BitVec.toNat_ofNat]
  congr 1
  change (i.val % 2 ^ 64) % 64 = i.val
  omega

/-- The flat basis is linearly independent over the binary prime field. -/
theorem flatBasis_linearIndependent : LinearIndependent (ZMod 2) flatBasis := by
  have h := binaryBasisVector_linearIndependent.map'
    wordBinaryAlgEquiv.symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr wordBinaryAlgEquiv.symm.injective)
  have he : (wordBinaryAlgEquiv.symm.toLinearMap ∘ binaryBasisVector) = flatBasis := by
    funext i
    apply wordBinaryAlgEquiv.injective
    change wordBinaryAlgEquiv (wordBinaryAlgEquiv.symm (binaryBasisVector i)) =
      (flatBasis i).toField
    rw [AlgEquiv.apply_symm_apply, flatBasis_toField]
  rw [he] at h
  exact h

instance : Fact (LinearIndependent (ZMod 2) flatBasis) := ⟨flatBasis_linearIndependent⟩

instance : Fact (flatBasis 0 = 1) := ⟨rfl⟩

end AdditiveNTT.Packed
