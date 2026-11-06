/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Word
public import CompPoly.Data.ByteArray.Packed

/-!
# Packed binary-field coordinates

Eight little-endian bytes per base-field word. Two existing 32-bit accessors load
or store a word; the arithmetic adds no foreign interface. Bounds and lengths
are carried as proofs and disappear from compiled kernels.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace BF64

/-- A byte buffer containing exactly `size` base-field words. -/
structure Packed where
  /-- Number of field elements. -/
  size : Nat
  /-- Little-endian coefficient words. -/
  bytes : ByteArray
  /-- Every word has eight bytes. -/
  byteSize : bytes.size = 8 * size

namespace Packed

/-- Allocate a zero-filled packed buffer. -/
def zeros (n : Nat) : Packed :=
  ⟨n, ByteArray.zeros (8 * n), ByteArray.size_zeros _⟩

/-- Load one word without allocating a boxed array element. -/
@[inline] def get (a : Packed) (i : Fin a.size) : Word :=
  ⟨(a.bytes.getUInt32LE (8 * i.val) (by have := a.byteSize; have := i.isLt; omega)).toUInt64 |||
    ((a.bytes.getUInt32LE (8 * i.val + 4)
      (by have := a.byteSize; have := i.isLt; omega)).toUInt64 <<< 32)⟩

/-- Store one word, preserving the buffer length. -/
@[inline] def set (a : Packed) (i : Fin a.size) (v : Word) : Packed :=
  let bytes := (a.bytes.setUInt32LE! (8 * i.val) v.val.toUInt32).setUInt32LE!
    (8 * i.val + 4) (v.val >>> 32).toUInt32
  ⟨a.size, bytes, by simp only [bytes, ByteArray.size_setUInt32LE!, a.byteSize]⟩

@[simp] theorem size_set (a : Packed) (i : Fin a.size) (v : Word) :
    (a.set i v).size = a.size := rfl

private theorem word_halves (v : UInt64) : v.toUInt32.toUInt64 |||
    ((v >>> 32).toUInt32.toUInt64 <<< 32) = v := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_toUInt32,
    UInt32.toBitVec_toUInt64, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.toNat_umod]
  by_cases h : i < 32
  · simp [h, hi]
  · simp [h, hi, show i - 32 < 64 by omega, show i - 32 < 32 by omega,
      show 32 + (i - 32) = i by omega]
/-- A store changes exactly its indexed word. -/
@[simp] theorem get_set (a : Packed) (i j : Fin a.size) (v : Word) :
    (a.set i v).get j = if i = j then v else a.get j := by
  by_cases he : i = j
  · subst j
    simp only [Packed.get, Packed.set, ByteArray.getUInt32LE]
    rw [ByteArray.getUInt32LE!_setUInt32LE!_of_disjoint _ _ _ _
      (by simp only [ByteArray.size_setUInt32LE!]; have := a.byteSize; have := i.isLt; omega)
      (by omega)]
    rw [ByteArray.getUInt32LE!_setUInt32LE!_self _ _ _
      (by have := a.byteSize; have := i.isLt; omega)]
    rw [ByteArray.getUInt32LE!_setUInt32LE!_self _ _ _
      (by simp only [ByteArray.size_setUInt32LE!]; have := a.byteSize; have := i.isLt; omega)]
    simp only [word_halves, ite_true]
  · have hij : i.val ≠ j.val := fun h => he (Fin.ext h)
    simp only [he, ite_false, Packed.get, Packed.set, ByteArray.getUInt32LE]
    rw [ByteArray.getUInt32LE!_setUInt32LE!_of_disjoint _ _ _ _
      (by simp only [ByteArray.size_setUInt32LE!]; have := a.byteSize; have := j.isLt; omega)
      (by omega)]
    rw [ByteArray.getUInt32LE!_setUInt32LE!_of_disjoint _ _ _ _
      (by have := a.byteSize; have := j.isLt; omega) (by omega)]
    rw [ByteArray.getUInt32LE!_setUInt32LE!_of_disjoint _ _ _ _
      (by simp only [ByteArray.size_setUInt32LE!]; have := a.byteSize; have := j.isLt; omega)
      (by omega)]
    rw [ByteArray.getUInt32LE!_setUInt32LE!_of_disjoint _ _ _ _
      (by have := a.byteSize; have := j.isLt; omega) (by omega)]

/-- Packed buffers with a fixed number of words. -/
abbrev Buffer (n : Nat) := {a : Packed // a.size = n}

/-- Read a word from a fixed-length buffer. -/
@[inline] def read (a : Buffer n) (i : Fin n) : Word :=
  a.val.get ⟨i.val, by rw [a.property]; exact i.isLt⟩

/-- Write a word into a fixed-length buffer. -/
@[inline] def write (a : Buffer n) (i : Fin n) (v : Word) : Buffer n :=
  ⟨a.val.set ⟨i.val, by rw [a.property]; exact i.isLt⟩ v, a.property⟩

@[simp] theorem read_write (a : Buffer n) (i j : Fin n) (v : Word) :
    read (write a i v) j = if i = j then v else read a j := by
  simp only [read, write, get_set, Fin.ext_iff]

/-- Materialize a coordinate function in contiguous storage. -/
def ofFn (n : Nat) (f : Fin n → Word) : Buffer n :=
  (List.finRange n).foldl (fun a i => write a i (f i)) ⟨zeros n, rfl⟩

/-- Reading a filled buffer recovers its defining coordinate function. -/
@[simp] theorem read_ofFn (n : Nat) (f : Fin n → Word) (i : Fin n) :
    read (ofFn n f) i = f i := by
  have hf : ∀ (xs : List (Fin n)) (a : Buffer n),
      read (xs.foldl (fun a j => write a j (f j)) a) i =
        if i ∈ xs then f i else read a i := by
    intro xs
    induction xs with
    | nil => intro a; rfl
    | cons j xs ih =>
      intro a
      rw [List.foldl_cons, ih, read_write]
      by_cases h : i ∈ xs
      · simp [h]
      · by_cases hj : j = i
        · subst j; simp [h]
        · have hji : i ≠ j := Ne.symm hj
          simp [h, hj, hji]
  exact (hf _ _).trans (ite_eq_left (List.mem_finRange i))

/-- Fixed-length packed storage encodes as its contiguous little-endian bytes. -/
instance : CompPoly.ByteCodec (Buffer n) where
  width := 8 * n
  toBytes a := ⟨a.val.bytes.data, by
    have h := a.val.byteSize
    rw [a.property] at h
    exact h⟩
  ofBytes? b := some ⟨⟨n, ⟨b.toArray⟩, b.size_toArray⟩, rfl⟩
  ofBytes?_toBytes a := by
    rcases a with ⟨⟨k, ⟨bytes⟩, h⟩, hk⟩
    change k = n at hk
    subst k
    rfl

end Packed
end BF64
