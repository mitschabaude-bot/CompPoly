/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.FixedMap
public import CompPoly.Fields.Binary.BF64.WordProofs

/-! # Refinement of prepared lookup products -/

@[expose] public section

namespace BF64.Word

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace NibbleMap

private def chunks (a : Word) : Word :=
  add (add (add
    (add (add (add (add (add (add (add (add (add (add (add (add
    (⟨((a.val >>> 0) &&& 15) <<< 0⟩)
    (⟨((a.val >>> 4) &&& 15) <<< 4⟩))
    (⟨((a.val >>> 8) &&& 15) <<< 8⟩))
    (⟨((a.val >>> 12) &&& 15) <<< 12⟩))
    (⟨((a.val >>> 16) &&& 15) <<< 16⟩))
    (⟨((a.val >>> 20) &&& 15) <<< 20⟩))
    (⟨((a.val >>> 24) &&& 15) <<< 24⟩))
    (⟨((a.val >>> 28) &&& 15) <<< 28⟩))
    (⟨((a.val >>> 32) &&& 15) <<< 32⟩))
    (⟨((a.val >>> 36) &&& 15) <<< 36⟩))
    (⟨((a.val >>> 40) &&& 15) <<< 40⟩))
    (⟨((a.val >>> 44) &&& 15) <<< 44⟩))
    (⟨((a.val >>> 48) &&& 15) <<< 48⟩))
    (⟨((a.val >>> 52) &&& 15) <<< 52⟩))
    (⟨((a.val >>> 56) &&& 15) <<< 56⟩))
    (⟨((a.val >>> 60) &&& 15) <<< 60⟩)

private theorem chunks_eq (a : Word) : chunks a = a := by
  apply toField_injective
  apply BF64.ext
  change ((((a.val.toBitVec >>> 0) &&& 15#64) <<< 0) ^^^
      (((a.val.toBitVec >>> 4) &&& 15#64) <<< 4) ^^^
      (((a.val.toBitVec >>> 8) &&& 15#64) <<< 8) ^^^
      (((a.val.toBitVec >>> 12) &&& 15#64) <<< 12) ^^^
      (((a.val.toBitVec >>> 16) &&& 15#64) <<< 16) ^^^
      (((a.val.toBitVec >>> 20) &&& 15#64) <<< 20) ^^^
      (((a.val.toBitVec >>> 24) &&& 15#64) <<< 24) ^^^
      (((a.val.toBitVec >>> 28) &&& 15#64) <<< 28) ^^^
      (((a.val.toBitVec >>> 32) &&& 15#64) <<< 32) ^^^
      (((a.val.toBitVec >>> 36) &&& 15#64) <<< 36) ^^^
      (((a.val.toBitVec >>> 40) &&& 15#64) <<< 40) ^^^
      (((a.val.toBitVec >>> 44) &&& 15#64) <<< 44) ^^^
      (((a.val.toBitVec >>> 48) &&& 15#64) <<< 48) ^^^
      (((a.val.toBitVec >>> 52) &&& 15#64) <<< 52) ^^^
      (((a.val.toBitVec >>> 56) &&& 15#64) <<< 56) ^^^
      (((a.val.toBitVec >>> 60) &&& 15#64) <<< 60)) = a.val.toBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

private theorem entry (s : Word) (slot digit : Nat) (hs : slot < 16) (hd : digit < 16) :
    Packed.read (ofScalar s).table ⟨slot * 16 + digit, by omega⟩ =
      Word.mul s ⟨UInt64.ofNat digit <<< UInt64.ofNat (4 * slot)⟩ := by
  simp only [ofScalar, Packed.read_ofFn]
  have hm : (slot * 16 + digit) % 16 = digit := by omega
  have hdv : (slot * 16 + digit) / 16 = slot := by omega
  rw [hm, hdv]

/-- A prepared map computes multiplication by its construction scalar. -/
@[simp] theorem toField_mul (s a : Word) :
    toField ((ofScalar s).mul a) = toField s * toField a := by
  have h (v : UInt64) : (v &&& 15).toNat < 16 := by
    rw [UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have he : toField ((ofScalar s).mul a) = toField s * toField (chunks a) := by
    simp only [mul, chunks, toField_add]
    rw [entry s 0 _ (by decide) (h _),
      entry s 1 _ (by decide) (h _),
      entry s 2 _ (by decide) (h _),
      entry s 3 _ (by decide) (h _),
      entry s 4 _ (by decide) (h _),
      entry s 5 _ (by decide) (h _),
      entry s 6 _ (by decide) (h _),
      entry s 7 _ (by decide) (h _),
      entry s 8 _ (by decide) (h _),
      entry s 9 _ (by decide) (h _),
      entry s 10 _ (by decide) (h _),
      entry s 11 _ (by decide) (h _),
      entry s 12 _ (by decide) (h _),
      entry s 13 _ (by decide) (h _),
      entry s 14 _ (by decide) (h _),
      entry s 15 _ (by decide) (h _)]
    simp only [Word.toField_mul]
    simp only [UInt64.ofNat_toNat]
    simp only [mul_add]
    rfl
  rw [he, chunks_eq]

end NibbleMap

namespace ByteMap

private def chunks (a : Word) : Word :=
  add (add (add
    (add (add (add (add
    (⟨((a.val >>> 0) &&& 255) <<< 0⟩)
    (⟨((a.val >>> 8) &&& 255) <<< 8⟩))
    (⟨((a.val >>> 16) &&& 255) <<< 16⟩))
    (⟨((a.val >>> 24) &&& 255) <<< 24⟩))
    (⟨((a.val >>> 32) &&& 255) <<< 32⟩))
    (⟨((a.val >>> 40) &&& 255) <<< 40⟩))
    (⟨((a.val >>> 48) &&& 255) <<< 48⟩))
    (⟨((a.val >>> 56) &&& 255) <<< 56⟩)

private theorem chunks_eq (a : Word) : chunks a = a := by
  apply toField_injective
  apply BF64.ext
  change ((((a.val.toBitVec >>> 0) &&& 255#64) <<< 0) ^^^
      (((a.val.toBitVec >>> 8) &&& 255#64) <<< 8) ^^^
      (((a.val.toBitVec >>> 16) &&& 255#64) <<< 16) ^^^
      (((a.val.toBitVec >>> 24) &&& 255#64) <<< 24) ^^^
      (((a.val.toBitVec >>> 32) &&& 255#64) <<< 32) ^^^
      (((a.val.toBitVec >>> 40) &&& 255#64) <<< 40) ^^^
      (((a.val.toBitVec >>> 48) &&& 255#64) <<< 48) ^^^
      (((a.val.toBitVec >>> 56) &&& 255#64) <<< 56)) = a.val.toBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

private theorem entry (s : Word) (slot digit : Nat) (hs : slot < 8) (hd : digit < 256) :
    Packed.read (ofScalar s).table ⟨slot * 256 + digit, by omega⟩ =
      Word.mul s ⟨UInt64.ofNat digit <<< UInt64.ofNat (8 * slot)⟩ := by
  simp only [ofScalar, Packed.read_ofFn]
  have hm : (slot * 256 + digit) % 256 = digit := by omega
  have hdv : (slot * 256 + digit) / 256 = slot := by omega
  rw [hm, hdv]

/-- A prepared map computes multiplication by its construction scalar. -/
@[simp] theorem toField_mul (s a : Word) :
    toField ((ofScalar s).mul a) = toField s * toField a := by
  have h (v : UInt64) : (v &&& 255).toNat < 256 := by
    rw [UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have he : toField ((ofScalar s).mul a) = toField s * toField (chunks a) := by
    simp only [mul, chunks, toField_add]
    rw [entry s 0 _ (by decide) (h _),
      entry s 1 _ (by decide) (h _),
      entry s 2 _ (by decide) (h _),
      entry s 3 _ (by decide) (h _),
      entry s 4 _ (by decide) (h _),
      entry s 5 _ (by decide) (h _),
      entry s 6 _ (by decide) (h _),
      entry s 7 _ (by decide) (h _)]
    simp only [Word.toField_mul]
    simp only [UInt64.ofNat_toNat]
    simp only [mul_add]
    rfl
  rw [he, chunks_eq]

end ByteMap

end BF64.Word
