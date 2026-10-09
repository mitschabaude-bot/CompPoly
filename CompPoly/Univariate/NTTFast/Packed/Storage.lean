/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Data.Bytes.UInt32
public import CompPoly.Data.ByteArray.Pack

/-! # Packed-word storage semantics for native FFT kernels -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Storage

/-- Pack words into consecutive four-byte little-endian slots. -/
def pack (words : Array UInt32) : ByteArray :=
  ⟨(ByteCodec.encodeList words.toList).toArray⟩

@[simp] theorem size_pack (words : Array UInt32) : (pack words).size = 4 * words.size := by
  simp only [pack, ByteArray.size, List.size_toArray, ByteCodec.length_encodeList,
    Array.length_toList, ByteCodec.width_uint32, Nat.mul_comm]

/-- Packing preserves concatenation of complete word slots. -/
theorem pack_append (xs ys : Array UInt32) : pack (xs ++ ys) = pack xs ++ pack ys := by
  apply ByteArray.ext
  simp only [pack, ByteArray.data_append, Array.toList_append, ByteCodec.encodeList,
    List.flatMap_append, List.append_toArray]

private theorem drop_encodeList (words : List UInt32) (index : Nat) :
    (ByteCodec.encodeList words).drop (4 * index) = ByteCodec.encodeList (words.drop index) := by
  induction index generalizing words with
  | zero => simp only [Nat.mul_zero, List.drop_zero]
  | succ index ih =>
    cases words with
    | nil => simp only [ByteCodec.encodeList_nil, List.drop_nil]
    | cons x xs =>
      have hx : (ByteCodec.toBytes x).toList.length = 4 := by
        simp only [Vector.length_toList, ByteCodec.width_uint32]
      rw [ByteCodec.encodeList_cons, List.drop_append,
        List.drop_of_length_le (show (ByteCodec.toBytes x).toList.length ≤ 4 * (index + 1) by
          rw [hx]; omega)]
      simp only [List.nil_append, hx]
      rw [show 4 * (index + 1) - 4 = 4 * index by omega, ih, List.drop_succ_cons]

private theorem take_encodeList (words : List UInt32) (count : Nat) :
    (ByteCodec.encodeList words).take (4 * count) = ByteCodec.encodeList (words.take count) := by
  induction count generalizing words with
  | zero => simp only [Nat.mul_zero, List.take_zero, ByteCodec.encodeList_nil]
  | succ count ih =>
    cases words with
    | nil => simp only [ByteCodec.encodeList_nil, List.take_nil]
    | cons x xs =>
      have hx : (ByteCodec.toBytes x).toList.length = 4 := by
        simp only [Vector.length_toList, ByteCodec.width_uint32]
      rw [ByteCodec.encodeList_cons,
        show 4 * (count + 1) = (ByteCodec.toBytes x).toList.length + 4 * count by rw [hx]; omega,
        List.take_length_add_append, ih, List.take_succ_cons, ByteCodec.encodeList_cons]

/-- Byte extraction on slot boundaries is word extraction. -/
theorem pack_extract (words : Array UInt32) (first last : Nat) :
    (pack words).data.extract (4 * first) (4 * last) = (pack (words.extract first last)).data := by
  apply Array.toList_inj.mp
  simp only [pack, Array.toList_extract, List.toList_toArray, List.extract,
    ← Nat.mul_sub_left_distrib, drop_encodeList, take_encodeList]

/-- Replace a byte range without changing the other bytes. -/
def replace (bytes : ByteArray) (offset : Nat) (values : ByteArray) : ByteArray :=
  ⟨bytes.data.extract 0 offset ++ values.data ++
    bytes.data.extract (offset + values.size) bytes.size⟩

/-- Replacing packed slots is exactly the corresponding word-array splice. -/
theorem replace_pack (words values : Array UInt32) (index : Nat) :
    replace (pack words) (4 * index) (pack values) =
      pack (words.extract 0 index ++ values ++ words.extract (index + values.size) words.size) := by
  simp only [replace, size_pack, pack_append]
  apply ByteArray.ext
  simp only [ByteArray.data_append]
  have hp := pack_extract words 0 index
  simp only [Nat.mul_zero] at hp
  rw [hp,
    show 4 * index + 4 * values.size = 4 * (index + values.size) by omega, pack_extract]

theorem size_replace (bytes values : ByteArray) (offset : Nat)
    (h : offset + values.size ≤ bytes.size) : (replace bytes offset values).size = bytes.size := by
  simp only [replace, ByteArray.size, Array.size_append, Array.size_extract]
  simp only [ByteArray.size] at h
  omega

theorem replace_empty (bytes : ByteArray) (offset : Nat) (h : offset ≤ bytes.size) :
    replace bytes offset ByteArray.empty = bytes := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [replace, ByteArray.size, Array.size_append, Array.size_extract]
    simp only [ByteArray.size] at h
    change min offset bytes.data.size - 0 + 0 +
      (min bytes.data.size bytes.data.size - (offset + 0)) = _
    omega
  · intro j h1 h2
    have he : ByteArray.empty.data.size = 0 := rfl
    simp only [ByteArray.size] at h
    simp only [replace, ByteArray.size, Array.getElem_append, Array.getElem_extract,
      Array.size_append, Array.size_extract]
    split_ifs <;> first | omega | (congr 1; omega)

/-- Replacing two adjacent byte ranges is replacing their concatenation. -/
theorem replace_replace (bytes p q : ByteArray) (offset : Nat)
    (h : offset + p.size + q.size ≤ bytes.size) :
    replace (replace bytes offset p) (offset + p.size) q = replace bytes offset (p ++ q) := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [replace, ByteArray.size, ByteArray.data_append, Array.size_append,
      Array.size_extract]
    simp only [ByteArray.size] at h
    omega
  · intro j h1 h2
    simp only [ByteArray.size] at h
    simp only [replace, ByteArray.size, ByteArray.data_append, Array.getElem_append,
      Array.getElem_extract, Array.size_append, Array.size_extract]
    split_ifs <;> first | omega | (congr 1; omega)

theorem replace_append_size (bytes z p : ByteArray) (hz : z.size = p.size) :
    replace (bytes ++ z) bytes.size p = bytes ++ p := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [replace, ByteArray.size, ByteArray.data_append, Array.size_append,
      Array.size_extract]
    simp only [ByteArray.size] at hz
    omega
  · intro j h1 h2
    simp only [ByteArray.size] at hz
    simp only [ByteArray.data_append, Array.size_append] at h2
    simp only [replace, ByteArray.size, ByteArray.data_append, Array.getElem_append,
      Array.getElem_extract, Array.size_append, Array.size_extract]
    split_ifs <;> first | omega | (congr 1; omega)

theorem toUInt8_shiftRight (v : UInt32) (s : UInt32) (k : Nat) (hs : s.toNat = 8 * k)
    (hk : k < 4) : (v >>> s).toUInt8 = UInt8.ofNat (v.toNat / 2 ^ (8 * k) % 256) := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    hs, Nat.mod_eq_of_lt (show 8 * k < 32 by omega), Nat.mod_mod]

/-- A little-endian word store replaces four bytes with the word's packed encoding. -/
theorem setUInt32LE!_eq_replace (bytes : ByteArray) (offset : Nat) (v : UInt32)
    (h : offset + 4 ≤ bytes.size) :
    bytes.setUInt32LE! offset v = replace bytes offset (pack #[v]) := by
  have hp : (pack #[v]).data = #[UInt8.ofNat (v.toNat % 256), UInt8.ofNat (v.toNat / 256 % 256),
      UInt8.ofNat (v.toNat / 256 / 256 % 256), UInt8.ofNat (v.toNat / 256 / 256 / 256 % 256)] := by
    simp only [pack, ByteCodec.encodeList_cons, ByteCodec.encodeList_nil,
      ByteCodec.toBytes_uint32, List.append_nil, Bytes.toListLE_succ, Bytes.toListLE_zero]
  have hv0 : v.toUInt8 = UInt8.ofNat (v.toNat % 256) := by
    have := toUInt8_shiftRight v 0 0 rfl (by decide)
    rwa [UInt32.shiftRight_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  have hv1 : (v >>> 8).toUInt8 = UInt8.ofNat (v.toNat / 256 % 256) :=
    toUInt8_shiftRight v 8 1 rfl (by decide)
  have hv2 : (v >>> 16).toUInt8 = UInt8.ofNat (v.toNat / 256 / 256 % 256) := by
    rw [Nat.div_div_eq_div_mul]; exact toUInt8_shiftRight v 16 2 rfl (by decide)
  have hv3 : (v >>> 24).toUInt8 = UInt8.ofNat (v.toNat / 256 / 256 / 256 % 256) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    exact toUInt8_shiftRight v 24 3 rfl (by decide)
  generalize pack #[v] = P at hp ⊢
  obtain ⟨d⟩ := P
  subst hp
  unfold ByteArray.setUInt32LE!
  rw [ite_eq_left h]
  apply ByteArray.ext
  apply Array.ext
  · simp only [replace, ByteArray.size, ByteArray.set!, Array.set!_eq_setIfInBounds,
      Array.size_setIfInBounds, Array.size_append, Array.size_extract, List.size_toArray,
      List.length_cons, List.length_nil]
    simp only [ByteArray.size] at h
    omega
  · intro j h1' h2'
    simp only [ByteArray.size] at h
    have hj : j < bytes.data.size := by
      simpa only [ByteArray.set!, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] using h1'
    simp only [ByteArray.set!, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by simp only [Array.size_setIfInBounds]; exact hj),
      Array.getElem_setIfInBounds (by simp only [Array.size_setIfInBounds]; exact hj),
      Array.getElem_setIfInBounds (by simp only [Array.size_setIfInBounds]; exact hj),
      Array.getElem_setIfInBounds hj]
    simp only [replace, ByteArray.size, Array.getElem_append, Array.getElem_extract,
      Array.size_append, Array.size_extract, List.size_toArray, List.length_cons,
      List.length_nil, hv0, hv1, hv2, hv3]
    split_ifs <;> first
      | omega | (congr 1; omega)
      | (simp only [show j - (min offset bytes.data.size - 0) = 0 by omega]; rfl)
      | (simp only [show j - (min offset bytes.data.size - 0) = 1 by omega]; rfl)
      | (simp only [show j - (min offset bytes.data.size - 0) = 2 by omega]; rfl)
      | (simp only [show j - (min offset bytes.data.size - 0) = 3 by omega]; rfl)

theorem set!_eq_splice (W : Array UInt32) (k : Nat) (v : UInt32) (hk : k < W.size) :
    W.set! k v = W.extract 0 k ++ #[v] ++ W.extract (k + 1) W.size := by
  apply Array.ext
  · simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.size_append,
      Array.size_extract, List.size_toArray, List.length_cons, List.length_nil]
    omega
  · intro j h1 h2
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at h1 ⊢
    rw [Array.getElem_setIfInBounds h1]
    simp only [Array.getElem_append, Array.getElem_extract, Array.size_extract, List.size_toArray,
      List.length_cons, List.length_nil, Array.size_append]
    split_ifs <;> first | omega | (congr 1; omega) |
      (simp only [show j - (min k W.size - 0) = 0 by omega]; rfl)

/-- A word store into packed words sets one word. -/
theorem setUInt32LE!_pack (W : Array UInt32) (k : Nat) (v : UInt32) :
    (pack W).setUInt32LE! (4 * k) v = pack (W.set! k v) := by
  by_cases hk : k < W.size
  · rw [setUInt32LE!_eq_replace _ _ _ (by rw [size_pack]; omega), replace_pack W #[v] k,
      set!_eq_splice W k v hk]
    rfl
  · have hs : W.set! k v = W := by
      simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, show ¬k < W.size from hk,
        ↓reduceDIte]
    rw [hs]
    unfold ByteArray.setUInt32LE!
    rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by rw [size_pack]; omega))]

/-- A word load from packed words reads one word. -/
theorem getUInt32LE!_pack (W : Array UInt32) (k : Nat) :
    (pack W).getUInt32LE! (4 * k) = W.getD k 0 := by
  by_cases hk : k < W.size
  · have h := ByteArray.getUInt32LE!_setUInt32LE!_self (pack W) (4 * k) (W[k])
      (by rw [size_pack]; omega)
    have hs : W.set! k W[k] = W := by
      apply Array.ext
      · simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      · intro j h1 _
        simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at h1 ⊢
        rw [Array.getElem_setIfInBounds h1]
        split
        · rename_i e; subst e; rfl
        · rfl
    rw [setUInt32LE!_pack, hs] at h
    rw [h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
  · unfold ByteArray.getUInt32LE!
    rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by rw [size_pack]; omega)),
      Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by omega), Option.getD_none]

end CompPoly.CPolynomial.NTTFast.Packed.Storage
