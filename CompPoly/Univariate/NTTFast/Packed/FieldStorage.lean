/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all Init.Data.Array.Basic
import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.StorageLemmas
public import CompPoly.Univariate.NTTFast.Packed.Arrays

/-! # Packed Montgomery field arrays -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Store the Montgomery coordinates of a field array. -/
def packFields (a : Array KoalaBear.Fast.Field) : ByteArray := Storage.pack (a.map Subtype.val)

@[simp] theorem size_packFields (a : Array KoalaBear.Fast.Field) :
    (packFields a).size = 4 * a.size := by
  simp only [packFields, Storage.size_pack, Array.size_map]

/-- Reading a mapped coordinate preserves the field array's zero default. -/
theorem getD_map_val (a : Array KoalaBear.Fast.Field) (i : Nat) :
    (a.map Subtype.val).getD i 0 = (a.getD i 0).val := by
  by_cases hi : i < a.size
  · have hm : i < (a.map Subtype.val).size := by simpa only [Array.size_map] using hi
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
      Array.getElem?_eq_getElem hm, Option.getD_some, Array.getElem_map]
  · have hm : ¬i < (a.map Subtype.val).size := by simpa only [Array.size_map] using hi
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hi),
      Array.getElem?_eq_none (Nat.le_of_not_lt hm), Option.getD_none]
    rfl

/-- Mapping coordinates commutes with extracting field-array segments. -/
theorem map_val_extract (a : Array KoalaBear.Fast.Field) (first last : Nat) :
    (a.extract first last).map Subtype.val = (a.map Subtype.val).extract first last := by
  apply Array.toList_inj.mp
  simp only [Array.toList_map, Array.toList_extract, List.extract, List.map_take, List.map_drop]

/-- Packing fields preserves concatenation. -/
theorem packFields_append (a b : Array KoalaBear.Fast.Field) :
    packFields (a ++ b) = packFields a ++ packFields b := by
  simp only [packFields, Array.map_append, Storage.pack_append]

/-- The compiled bounded word read returns the exact field coordinate. -/
theorem Native.readUOffset_packFields (a : Array KoalaBear.Fast.Field) (i o : USize) (h) :
    Native.readUOffset (packFields a) i o h = (a.getD (i.toNat + o.toNat) 0).val := by
  exact (Native.readUOffset_pack (a.map Subtype.val) i o h).trans (getD_map_val a _)

/-- A checked ordinary read agrees with the represented field coordinate. -/
theorem Native.read_packFields (a : Array KoalaBear.Fast.Field) (i : Nat)
    (hs : (packFields a).size < USize.size) (hi : i < a.size) :
    Native.read (packFields a) i = (a.getD i 0).val := by
  exact (Native.read_pack (a.map Subtype.val) i hs
    (by simpa only [Array.size_map] using hi)).trans (getD_map_val a i)

/-- A single word append has its ordinary packed-array semantics. -/
theorem Native.push_eq (b : ByteArray) (x : UInt32) :
    Native.push b x = b ++ Storage.pack #[x] := by
  rw [Native.push, Native.storeWords_eq]
  rfl

/-- Packing an empty field array gives an empty byte buffer. -/
@[simp] theorem packFields_empty : packFields (#[] : Array KoalaBear.Fast.Field) =
  ByteArray.empty := by
  unfold packFields Storage.pack
  simp only [Array.map_empty, Array.toList_empty, ByteCodec.encodeList, List.flatMap_nil]
  rfl

/-- A field-coordinate batch store realizes the corresponding array splice. -/
theorem Native.write16_packFields (a : Array KoalaBear.Fast.Field) (i : Nat)
    (hs : (packFields a).size < USize.size) (hi : i + 16 ≤ a.size)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : KoalaBear.Fast.Field) :
    Native.write16 (packFields a) i x0.val x1.val x2.val x3.val x4.val x5.val x6.val x7.val
      x8.val x9.val x10.val x11.val x12.val x13.val x14.val x15.val =
      packFields (splice a i #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        x15]) := by
  have hin : i < USize.size := by rw [size_packFields] at hs; omega
  have hmul : i * 4 < USize.size := by rw [size_packFields] at hs; omega
  have ho : (i.toUSize * 4).toNat = 4 * i := by
    rw [USize.toNat_mul, USize.toNat_ofNat_of_lt' hin,
      Native.usize_numeral 4 (by decide), Nat.mod_eq_of_lt hmul]
    omega
  have hc : (16 : UInt8).toNat ≤ 16 := by decide
  have hvalues : (#[x0.val, x1.val, x2.val, x3.val, x4.val, x5.val, x6.val, x7.val, x8.val,
    x9.val, x10.val, x11.val, x12.val, x13.val, x14.val, x15.val] : Array UInt32) = (#[x0, x1,
    x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]).map Subtype.val := by
    apply Array.toList_inj.mp
    simp only [Array.toList_map]
    rfl
  unfold Native.write16 packFields
  rw [Native.storeWords_replace_pack (a.map Subtype.val) (i.toUSize * 4) 16 i hc ho
    (by simpa only [Array.size_map, show (16 : UInt8).toNat = 16 by decide] using hi) hs]
  simp only [show (16 : UInt8).toNat = 16 by decide]
  change Storage.pack
    ((a.map Subtype.val).extract 0 i ++ #[x0.val, x1.val, x2.val, x3.val, x4.val, x5.val, x6.val,
      x7.val, x8.val, x9.val, x10.val, x11.val, x12.val, x13.val, x14.val, x15.val].extract 0 16 ++
      (a.map Subtype.val).extract (i + 16) (a.map Subtype.val).size) = _
  have hv : #[x0.val, x1.val, x2.val, x3.val, x4.val, x5.val, x6.val, x7.val, x8.val, x9.val,
    x10.val, x11.val, x12.val, x13.val, x14.val, x15.val].extract 0 16 = #[x0.val, x1.val,
    x2.val, x3.val, x4.val, x5.val, x6.val, x7.val, x8.val, x9.val, x10.val, x11.val, x12.val,
    x13.val, x14.val, x15.val] := Array.extract_size
  rw [hv, hvalues]
  simp only [splice, Array.map_append, map_val_extract, Array.size_map]
  rfl

/-- `n` zero words represent `n` zero coordinates. -/
theorem Native.zeroWords_packFields (n : Nat) :
    Native.zeroWords n = packFields (Array.replicate n 0) := by
  rw [Native.zeroWords_eq, packFields, Array.map_replicate]
  rfl

/-- A batch store at the end of a written prefix extends the prefix and consumes the batch's
slots of the rest. -/
theorem Native.write16U_cursor (l Z : Array KoalaBear.Fast.Field) (p : USize)
    (hp : p.toNat = l.size) (hZ : 16 ≤ Z.size) (hs : (packFields (l ++ Z)).size < USize.size)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : KoalaBear.Fast.Field) :
    Native.write16U (packFields (l ++ Z)) p x0.val x1.val x2.val x3.val x4.val x5.val x6.val
      x7.val x8.val x9.val x10.val x11.val x12.val x13.val x14.val x15.val =
      packFields (l ++ #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++
        Z.extract 16 Z.size) := by
  rw [Native.write16U_eq, Native.write16_packFields _ _ hs
    (by rw [Array.size_append]; omega), hp,
    splice_cursor l Z #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] hZ]
  rfl

/-- Appending a complete field-coordinate batch preserves its packed representation. -/
theorem Native.push16_packFields (a : Array KoalaBear.Fast.Field)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : KoalaBear.Fast.Field) :
    Native.push16 (packFields a) x0.val x1.val x2.val x3.val x4.val x5.val x6.val x7.val x8.val
      x9.val x10.val x11.val x12.val x13.val x14.val x15.val =
      packFields (a ++ #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        x15]) := by
  unfold Native.push16 packFields
  rw [Native.storeWords_append_pack (a.map Subtype.val) 0 16 (by decide)]
  simp only [show (16 : UInt8).toNat = 16 by decide, Array.map_append]
  have hv : (#[x0.val, x1.val, x2.val, x3.val, x4.val, x5.val, x6.val, x7.val, x8.val, x9.val,
    x10.val, x11.val, x12.val, x13.val, x14.val, x15.val] : Array UInt32).extract 0 16 =
    #[x0.val, x1.val, x2.val, x3.val, x4.val, x5.val, x6.val, x7.val, x8.val, x9.val, x10.val,
    x11.val, x12.val, x13.val, x14.val, x15.val] := Array.extract_size
  rw [hv]
  congr 2
  apply Array.toList_inj.mp
  simp only [Array.toList_map]
  rfl

/-- A bounded single-coordinate write implements the corresponding field-array update. -/
theorem Native.write_packFields (a : Array KoalaBear.Fast.Field) (i : Nat)
    (hs : (packFields a).size < USize.size) (hi : i < a.size)
    (x : KoalaBear.Fast.Field) :
    Native.write (packFields a) i x.val = packFields (a.setIfInBounds i x) := by
  have hin : i < USize.size := by rw [size_packFields] at hs; omega
  have hmul : i * 4 < USize.size := by rw [size_packFields] at hs; omega
  have ho : (i.toUSize * 4).toNat = 4 * i := by
    rw [USize.toNat_mul, USize.toNat_ofNat_of_lt' hin,
      Native.usize_numeral 4 (by decide), Nat.mod_eq_of_lt hmul]
    omega
  unfold Native.write packFields
  rw [Native.storeWords_replace_pack (a.map Subtype.val) (i.toUSize * 4) 1 i (by decide) ho
    (by simp only [Array.size_map, show (1 : UInt8).toNat = 1 by decide]; omega) hs]
  simp only [show (1 : UInt8).toNat = 1 by decide]
  change Storage.pack ((a.map Subtype.val).extract 0 i ++ #[x.val] ++
    (a.map Subtype.val).extract (i + 1) (a.map Subtype.val).size) = _
  rw [← splice_singleton a i x hi]
  simp only [splice, Array.map_append, map_val_extract, Array.size_map, Array.size_singleton,
    Array.map_singleton]

theorem Native.encodeGo_packFields (a c : Array KoalaBear.Fast.Field) (hs : (packFields a).size <
    USize.size) : ∀ (n i : Nat), c.size = a.size → i + n = a.size →
    Native.encodeGo a n i (packFields c) = packFields (c.extract 0 i ++ a.extract i a.size) := by
  intro n
  induction n generalizing c with
  | zero =>
    intro i hc hi
    simp only [Native.encodeGo, Nat.add_zero] at hi ⊢
    have e1 : a.extract a.size a.size = #[] := Array.extract_eq_empty_of_le (by omega)
    have e2 : c.extract 0 a.size = c := by rw [← hc, Array.extract_size]
    rw [hi, e1, e2, Array.append_empty]
  | succ n ih =>
    intro i hc hi
    rw [Native.encodeGo, Native.write_packFields c i (by
      rw [size_packFields, hc]; rw [size_packFields] at hs; exact hs)
      (by omega), ih _ (i + 1) (by simp only [Array.size_setIfInBounds, hc]) (by omega)]
    congr 1
    apply Array.ext
    · simp only [Array.size_append, Array.size_extract, Array.size_setIfInBounds]
      omega
    · intro j h1 h2
      simp only [Array.getElem_append, Array.getElem_extract, Array.size_extract,
        Array.size_setIfInBounds, Nat.zero_add, Nat.sub_zero]
      split_ifs with ha hb hb
      · rw [Array.getElem_setIfInBounds]
        split
        · omega
        · rfl
      · rw [Array.getElem_setIfInBounds]
        split
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
          simp only [show i + (j - min i c.size) = i by omega]
        · omega
        · omega
      · omega
      · simp only [show i + 1 + (j - min (i + 1) c.size) = i + (j - min i c.size) by omega]

/-- The executable encoder realizes the packed field-array representation. -/
theorem Native.encode_eq (a : Array KoalaBear.Fast.Field) : Native.encode a = packFields a := by
  unfold Native.encode
  split
  · rename_i hs
    rw [Native.zeroWords_packFields, Native.encodeGo_packFields a _
      (by rwa [size_packFields]) _ 0 Array.size_replicate (by omega)]
    simp only [Array.extract_zero, Array.empty_append, Array.extract_size]
  · rfl

end CompPoly.CPolynomial.NTTFast.Packed
