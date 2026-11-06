/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Xor
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.ScratchProofs
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Correctness
/-! # Certified forward and inverse bit-plane butterflies -/
@[expose] public section
namespace AdditiveNTT.Bitsliced
open BF64

/-- Apply the forward butterfly to two rows and reuse its combination scratch. -/
@[inline] def forwardKernel (m : Block) (u v : Block) (s : Scratch) : (Block × Block) × Scratch :=
  let s := prepareScratch s v
  let lo := u.xor (applyScratch s m)
  ((lo, lo.xor v), s)

/-- Apply the inverse butterfly with the forward butterfly's shared twiddle. -/
@[inline] def inverseKernel (m : Block) (u v : Block) (s : Scratch) : (Block × Block) × Scratch :=
  let hi := u.xor v
  let s := prepareScratch s hi
  ((u.xor (applyScratch s m), hi), s)

/-- Forward butterfly in the mathematical matrix model. -/
def forwardOp (t : UInt64) (u v : Block) : Block × Block :=
  let lo := u.xor (applySpec t v)
  (lo, lo.xor v)

/-- Inverse butterfly in the mathematical matrix model. -/
def inverseOp (t : UInt64) (u v : Block) : Block × Block :=
  let hi := u.xor v
  (u.xor (applySpec t hi), hi)

/-- Every native forward butterfly agrees with the mathematical matrix model. -/
theorem forwardKernel_correct (t : UInt64) (u v : Block) (s : Scratch) :
    (forwardKernel (matrix t) u v s).1 = forwardOp t u v := by
  simp only [forwardKernel, forwardOp, applyScratch_eq_applySpec]

/-- Every native inverse butterfly agrees with the mathematical matrix model. -/
theorem inverseKernel_correct (t : UInt64) (u v : Block) (s : Scratch) :
    (inverseKernel (matrix t) u v s).1 = inverseOp t u v := by
  simp only [inverseKernel, inverseOp, applyScratch_eq_applySpec]

/-- Plane-wise word XOR is addition in every decoded lane. -/
theorem lane_xor (u v : Block) (j : Fin 64) :
    (lane (u.xor v) j).toField = (lane u j).toField + (lane v j).toField := by
  apply coordinate_ext
  intro i
  simp only [coordinate_lane, Block.get_xor, toField_xor, map_add]

/-- Decoding the forward bit-plane butterfly gives the certified packed butterfly. -/
theorem forwardOp_lane (m : Packed.Multiplier) (u v : Block) (j : Fin 64) :
    (lane (forwardOp m.scalar.val u v).1 j,
      lane (forwardOp m.scalar.val u v).2 j) = Packed.forwardPair m (lane u j) (lane v j) := by
  apply Prod.ext
  · apply Word.toField_injective
    simp only [forwardOp, lane_xor, lane_applySpec, Packed.forwardPair, Word.toField_add, m.correct]
  · apply Word.toField_injective
    simp only [forwardOp, lane_xor, lane_applySpec, Packed.forwardPair, Word.toField_add, m.correct]

/-- Decoding the inverse bit-plane butterfly gives the certified packed inverse. -/
theorem inverseOp_lane (m : Packed.Multiplier) (u v : Block) (j : Fin 64) :
    (lane (inverseOp m.scalar.val u v).1 j,
      lane (inverseOp m.scalar.val u v).2 j) = Packed.inversePair m (lane u j) (lane v j) := by
  apply Prod.ext
  · apply Word.toField_injective
    simp only [inverseOp, lane_xor, lane_applySpec, Packed.inversePair, Word.toField_add, m.correct]
  · apply Word.toField_injective
    simp only [inverseOp, lane_xor, Packed.inversePair, Word.toField_add]

end AdditiveNTT.Bitsliced
