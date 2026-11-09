/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.Packed
import Mathlib.Tactic.IntervalCases

/-! # Extensionality of packed binary-field buffers -/

@[expose] public section

namespace ByteArray

theorem getUInt32LE!_byte (a : ByteArray) (off k : Nat)
    (ho : off + 4 ≤ a.size) (hk : k < 4) :
    ((a.getUInt32LE! off) >>> UInt32.ofNat (8 * k)).toUInt8 = a[off + k]! := by
  unfold getUInt32LE!
  rw [ite_eq_left ho]
  simp only [get!_eq_getElem!]
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases k <;>
    simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.add_zero,
      UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
      UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32, BitVec.shiftLeft_eq',
      BitVec.ushiftRight_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.toNat_umod] <;>
    simp (disch := omega) [UInt32.toBitVec_ofNat,
      BitVec.getLsbD_of_ge, hj, show j < 16 by omega, show j < 24 by omega,
      show j < 32 by omega, show 8 + j < 16 by omega, show 8 + j < 24 by omega,
      show 8 + j < 32 by omega, show 16 + j < 24 by omega,
      show 16 + j < 32 by omega, show 24 + j < 32 by omega]

end ByteArray

namespace BF64.Packed

private theorem halves_lo (a b : UInt32) :
    (a.toUInt64 ||| (b.toUInt64 <<< 32)).toUInt32 = a := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) only [UInt64.toUInt32_or, UInt32.toUInt32_toUInt64,
    UInt32.toBitVec_or, UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftLeft,
    UInt32.toBitVec_toUInt64, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
    BitVec.reduceMod, BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, BitVec.setWidth_shiftLeft_of_le, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, BitVec.shiftLeft_eq_zero, BitVec.or_zero,
    BitVec.getLsbD_eq_getElem]

private theorem halves_hi (a b : UInt32) :
    ((a.toUInt64 ||| (b.toUInt64 <<< 32)) >>> 32).toUInt32 = b := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_or, UInt32.toBitVec_toUInt64, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceMod,
    BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    BitVec.ushiftRight_eq', BitVec.getLsbD_eq_getElem, BitVec.getElem_setWidth,
    BitVec.getElem_ushiftRight, BitVec.getElem_or, BitVec.getLsbD_of_ge,
    BitVec.getElem_shiftLeft, show ¬32 + i < 32 by omega, decide_false,
    Bool.not_false, add_tsub_cancel_left, Bool.true_and, Bool.false_or]

/-- Every word determines its eight physical bytes. -/
theorem read_ext (a b : Buffer n) (h : ∀ i, read a i = read b i) : a = b := by
  have hs : a.val.bytes.size = b.val.bytes.size := by
    rw [a.val.byteSize, b.val.byteSize, a.property, b.property]
  have hb : a.val.bytes = b.val.bytes := by
    apply ByteArray.ext_getElem hs
    intro j hj hj'
    have hja : j < 8 * n := by simpa only [a.val.byteSize, a.property] using hj
    let i : Fin n := ⟨j / 8, by omega⟩
    have he := h i
    have hlo := congrArg (fun w : BF64.Word => w.val.toUInt32) he
    have hhi := congrArg (fun w : BF64.Word => (w.val >>> 32).toUInt32) he
    simp only [read, get, ByteArray.getUInt32LE, halves_lo] at hlo
    simp only [read, get, ByteArray.getUInt32LE, halves_hi] at hhi
    have hsizea : a.val.bytes.size = 8 * n := by rw [a.val.byteSize, a.property]
    have hsizeb : b.val.bytes.size = 8 * n := by rw [b.val.byteSize, b.property]
    by_cases low : j % 8 < 4
    · have e := congrArg (fun v : UInt32 => (v >>> UInt32.ofNat (8 * (j % 8))).toUInt8) hlo
      rw [ByteArray.getUInt32LE!_byte _ _ _ (by rw [hsizea]; dsimp [i]; omega) low,
        ByteArray.getUInt32LE!_byte _ _ _ (by rw [hsizeb]; dsimp [i]; omega) low] at e
      have idx : 8 * i.val + j % 8 = j := by dsimp [i]; omega
      simpa only [idx, getElem!_pos a.val.bytes j hj, getElem!_pos b.val.bytes j hj'] using e
    · have e := congrArg (fun v : UInt32 => (v >>> UInt32.ofNat (8 * (j % 8 - 4))).toUInt8) hhi
      have hk : j % 8 - 4 < 4 := by omega
      rw [ByteArray.getUInt32LE!_byte _ _ _ (by rw [hsizea]; dsimp [i]; omega) hk,
        ByteArray.getUInt32LE!_byte _ _ _ (by rw [hsizeb]; dsimp [i]; omega) hk] at e
      have idx : 8 * i.val + 4 + (j % 8 - 4) = j := by dsimp [i]; omega
      simpa only [idx, getElem!_pos a.val.bytes j hj, getElem!_pos b.val.bytes j hj'] using e
  apply Subtype.ext
  rcases a with ⟨⟨asz, ab, ha⟩, ea⟩
  rcases b with ⟨⟨bsz, bb, hb'⟩, eb⟩
  change asz = n at ea
  change bsz = n at eb
  subst asz
  subst bsz
  cases hb
  rfl

end BF64.Packed
