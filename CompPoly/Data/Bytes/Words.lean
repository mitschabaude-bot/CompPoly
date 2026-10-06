/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import Init
import Mathlib.Tactic.SplitIfs

universe u

/-!
# 32-bit words in byte arrays

Tasks share their results with other threads. The runtime marks a shared array of boxed
values element by element, while a `ByteArray` is a scalar array and is marked at once. These
helpers store 32-bit words in a `ByteArray` with the core byte operations only, and give every
operation a word-level specification through `wordAt`.

`Word32Repr R` is a raw 32-bit representation of `R` with a decoder that recovers every
encoded value. Unlike `ByteCodec`, it describes the carrier, not the value: a Montgomery field
stores its residue as is.
-/

@[expose] public section

namespace CompPoly

/-- A raw 32-bit representation of `R`. -/
class Word32Repr (R : Type u) where
  /-- The stored word of a value. -/
  toWord : R → UInt32
  /-- The value of a stored word. -/
  ofWord : UInt32 → R
  ofWord_toWord (x : R) : ofWord (toWord x) = x

attribute [simp] Word32Repr.ofWord_toWord

namespace ByteWords

/-- Byte `i` of `b`; zero past the end. -/
def byteAt (b : ByteArray) (i : Nat) : UInt8 := b.data.getD i 0

/-- The little-endian word stored in bytes `4 k, …, 4 k + 3`. -/
def wordAt (b : ByteArray) (k : Nat) : UInt32 :=
  (byteAt b (4 * k)).toUInt32 + (byteAt b (4 * k + 1)).toUInt32 * (256 : UInt32) +
    (byteAt b (4 * k + 2)).toUInt32 * (65536 : UInt32) +
    (byteAt b (4 * k + 3)).toUInt32 * (16777216 : UInt32)

/-- The four bytes of a word recombine to the word. -/
theorem recombine (v : UInt32) :
    v.toUInt8.toUInt32 + (v >>> 8).toUInt8.toUInt32 * (256 : UInt32) +
      (v >>> 16).toUInt8.toUInt32 * (65536 : UInt32) +
      (v >>> 24).toUInt8.toUInt32 * (16777216 : UInt32) = v := by
  apply UInt32.toNat_inj.mp
  have hv := v.toNat_lt
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
    UInt32.toNat_shiftRight, UInt32.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reduceMod, Nat.reducePow] at *
  omega

/-- The four bytes of word `k` sit at machine indices without overflow. -/
theorem toNat_bytes (k : USize) (n : Nat) (h : 4 * k.toNat + 4 ≤ n) (hu : n < USize.size) :
    (4 * k).toNat = 4 * k.toNat ∧ (4 * k + 1).toNat = 4 * k.toNat + 1 ∧
      (4 * k + 2).toNat = 4 * k.toNat + 2 ∧ (4 * k + 3).toNat = 4 * k.toNat + 3 := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [USize.toNat_add, USize.toNat_mul, USize.reduceToNat, Nat.mod_add_mod, hsize] <;>
    exact Nat.mod_eq_of_lt (by omega)

/-- Read word `k`, whose bytes are in range. -/
@[inline] def readWordU (b : @& ByteArray) (k : USize) (n : Nat) (h : 4 * k.toNat + 4 ≤ n)
    (hn : n ≤ b.size) (hu : n < USize.size) : UInt32 :=
  have hb := toNat_bytes k n h hu
  (b.uget (4 * k) (by rw [hb.1]; omega)).toUInt32 +
    (b.uget (4 * k + 1) (by rw [hb.2.1]; omega)).toUInt32 * (256 : UInt32) +
    (b.uget (4 * k + 2) (by rw [hb.2.2.1]; omega)).toUInt32 * (65536 : UInt32) +
    (b.uget (4 * k + 3) (by rw [hb.2.2.2]; omega)).toUInt32 * (16777216 : UInt32)

theorem uget_eq_byteAt (b : ByteArray) (i : USize) (h : i.toNat < b.size) (n : Nat)
    (hn : i.toNat = n) : b.uget i h = byteAt b n := by
  subst hn
  simp only [ByteArray.uget, byteAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h,
    Option.getD_some]
  rfl

theorem readWordU_eq (b : ByteArray) (k : USize) (n : Nat) (h : 4 * k.toNat + 4 ≤ n)
    (hn : n ≤ b.size) (hu : n < USize.size) : readWordU b k n h hn hu = wordAt b k.toNat := by
  obtain ⟨h0, h1, h2, h3⟩ := toNat_bytes k n h hu
  unfold readWordU wordAt
  dsimp only
  rw [uget_eq_byteAt _ _ _ _ h0, uget_eq_byteAt _ _ _ _ h1, uget_eq_byteAt _ _ _ _ h2,
    uget_eq_byteAt _ _ _ _ h3]

theorem toNat_usize_le (b : ByteArray) : b.usize.toNat ≤ b.size := by
  simp only [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat']
  exact Nat.mod_le _ _

/-- Word `k` of `b`; zero unless its bytes are in range. -/
@[inline] def readWord (b : @& ByteArray) (k : USize) : UInt32 :=
  if h : k < b.usize / 4 then
    have hk : k.toNat < b.usize.toNat / 4 := by
      rw [USize.lt_iff_toNat_lt, USize.toNat_div] at h
      simpa only [USize.reduceToNat] using h
    readWordU b k b.usize.toNat (by omega) (toNat_usize_le b) b.usize.toNat_lt_size
  else 0

theorem readWord_eq (b : ByteArray) (k : USize) (h : 4 * k.toNat + 4 ≤ b.size)
    (hu : b.size < USize.size) : readWord b k = wordAt b k.toNat := by
  have hus : b.usize.toNat = b.size := by
    simp only [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat']
    exact Nat.mod_eq_of_lt hu
  unfold readWord
  rw [dite_eq_left_of_eq_true (eq_true (by
    rw [USize.lt_iff_toNat_lt, USize.toNat_div, hus]; simp only [USize.reduceToNat]; omega))]
  exact readWordU_eq _ _ _ _ _ _

theorem byteAt_uset (b : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < b.size) (j : Nat) :
    byteAt (b.uset i v h) j = if i.toNat = j then v else byteAt b j := by
  simp only [byteAt, ByteArray.uset, Array.uset, Array.getD_eq_getD_getElem?,
    Array.getElem?_set]
  split <;> rename_i hij
  · subst hij
    simp only [Option.getD_some]
  · rfl

@[simp] theorem size_uset (b : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < b.size) :
    (b.uset i v h).size = b.size := by
  simp only [ByteArray.size, ByteArray.uset, Array.size_uset]

/-- Store `v` as word `k`, whose bytes are in range. -/
@[inline] def writeWordU (b : ByteArray) (k : USize) (v : UInt32) (h : 4 * k.toNat + 4 ≤ b.size)
    (hu : b.size < USize.size) : ByteArray :=
  have hb := toNat_bytes k _ h hu
  let b1 := b.uset (4 * k) v.toUInt8 (by rw [hb.1]; omega)
  let b2 := b1.uset (4 * k + 1) (v >>> 8).toUInt8
    (by simp only [b1, size_uset]; rw [hb.2.1]; omega)
  let b3 := b2.uset (4 * k + 2) (v >>> 16).toUInt8
    (by simp only [b2, b1, size_uset]; rw [hb.2.2.1]; omega)
  b3.uset (4 * k + 3) (v >>> 24).toUInt8
    (by simp only [b3, b2, b1, size_uset]; rw [hb.2.2.2]; omega)

@[simp] theorem size_writeWordU (b : ByteArray) (k : USize) (v : UInt32)
    (h : 4 * k.toNat + 4 ≤ b.size) (hu : b.size < USize.size) :
    (writeWordU b k v h hu).size = b.size := by
  simp only [writeWordU, size_uset]

theorem byteAt_writeWordU (b : ByteArray) (k : USize) (v : UInt32)
    (h : 4 * k.toNat + 4 ≤ b.size) (hu : b.size < USize.size) (i : Nat) :
    byteAt (writeWordU b k v h hu) i =
      if i = 4 * k.toNat then v.toUInt8 else if i = 4 * k.toNat + 1 then (v >>> 8).toUInt8
      else if i = 4 * k.toNat + 2 then (v >>> 16).toUInt8
      else if i = 4 * k.toNat + 3 then (v >>> 24).toUInt8 else byteAt b i := by
  obtain ⟨h0, h1, h2, h3⟩ := toNat_bytes k _ h hu
  simp only [writeWordU, byteAt_uset, h0, h1, h2, h3]
  split_ifs <;> first | rfl | omega

theorem byteAt_writeWordU_of_lt (b : ByteArray) (k : USize) (v : UInt32)
    (h : 4 * k.toNat + 4 ≤ b.size) (hu : b.size < USize.size) (i : Nat)
    (hi : i < 4 * k.toNat ∨ 4 * k.toNat + 4 ≤ i) :
    byteAt (writeWordU b k v h hu) i = byteAt b i := by
  rw [byteAt_writeWordU]
  split_ifs <;> first | rfl | omega

theorem wordAt_writeWordU (b : ByteArray) (k : USize) (v : UInt32)
    (h : 4 * k.toNat + 4 ≤ b.size) (hu : b.size < USize.size) (j : Nat) :
    wordAt (writeWordU b k v h hu) j = if j = k.toNat then v else wordAt b j := by
  unfold wordAt
  by_cases hj : j = k.toNat
  · subst hj
    simp only [byteAt_writeWordU, ↓reduceIte, Nat.add_eq_left, Nat.add_left_cancel_iff,
      Nat.reduceEqDiff, Nat.succ_ne_zero]
    exact recombine v
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hj),
      byteAt_writeWordU_of_lt _ _ _ _ _ _ (by omega), byteAt_writeWordU_of_lt _ _ _ _ _ _ (by omega),
      byteAt_writeWordU_of_lt _ _ _ _ _ _ (by omega), byteAt_writeWordU_of_lt _ _ _ _ _ _ (by omega)]

theorem size_copySlice_self (b : ByteArray) (len : Nat) (hl : len ≤ b.size) :
    (b.copySlice 0 b b.size len).size = b.size + len := by
  simp only [ByteArray.copySlice, ByteArray.size, Array.size_append, Array.size_extract]
  simp only [ByteArray.size] at hl
  omega

/-- Double `b` until `n` bytes remain to fill, then fill them. -/
def zeroGo (n : Nat) (b : ByteArray) : Nat → ByteArray
  | 0 => b
  | fuel + 1 =>
    if 2 * b.size ≤ n then zeroGo n (b.copySlice 0 b b.size b.size) fuel
    else b.copySlice 0 b b.size (n - b.size)

theorem size_zeroGo (n : Nat) : ∀ (fuel : Nat) (b : ByteArray), 0 < b.size → b.size ≤ n →
    n < 2 ^ fuel * b.size → (zeroGo n b fuel).size = n := by
  intro fuel
  induction fuel with
  | zero => intro b _ h1 h2; simp only [Nat.pow_zero, Nat.one_mul] at h2; omega
  | succ fuel ih =>
    intro b h0 h1 h2
    rw [zeroGo]
    split
    · rename_i hle
      apply ih _ (by rw [size_copySlice_self _ _ (Nat.le_refl _)]; omega)
        (by rw [size_copySlice_self _ _ (Nat.le_refl _)]; omega)
      rw [size_copySlice_self _ _ (Nat.le_refl _), show b.size + b.size = 2 * b.size by omega,
        ← Nat.mul_assoc, ← Nat.pow_succ]
      exact h2
    · rw [size_copySlice_self _ _ (by omega)]; omega

/-- A buffer of `n` bytes, filled by doubling copies. Its contents are unspecified. -/
def buffer (n : Nat) : ByteArray :=
  if n = 0 then ByteArray.empty else zeroGo n ((ByteArray.emptyWithCapacity n).push 0) n

@[simp] theorem size_buffer (n : Nat) : (buffer n).size = n := by
  unfold buffer
  split
  · subst n; rfl
  · rename_i hn
    have h1 : ((ByteArray.emptyWithCapacity n).push 0).size = 1 := rfl
    apply size_zeroGo n n _ (by omega) (by omega)
    rw [h1, Nat.mul_one]
    exact Nat.lt_two_pow_self

end ByteWords

end CompPoly
