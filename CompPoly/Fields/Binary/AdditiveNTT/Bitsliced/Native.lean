/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Fold
/-! # Checked machine-word addressing for packed bit-plane buffers -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace AdditiveNTT.Bitsliced
namespace Native

/-- Small numerals are represented exactly on every supported machine. -/
theorem small (n : Nat) (h : n < 4294967296) :
    (no_index (OfNat.ofNat n : USize)).toNat = n :=
  USize.toNat_ofNat_of_lt (lt_of_lt_of_le h USize.le_size)

/-- Addition does not wrap within a small packed buffer. -/
theorem add_toNat (i j : USize) (h : i.toNat + j.toNat < 4294967296) :
    (i + j).toNat = i.toNat + j.toNat := by
  rw [USize.toNat_add, Nat.mod_eq_of_lt (lt_of_lt_of_le h USize.le_size)]

/-- Byte offset of an indexed packed word. -/
theorem offset_toNat (i : USize) (hi : i.toNat < n) (hn : 8 * n < 4294967296) :
    (i * 8).toNat = 8 * i.toNat := by
  rw [USize.toNat_mul, small 8 (by decide), Nat.mod_eq_of_lt]
  · omega
  · exact lt_of_lt_of_le (by omega) USize.le_size

/-- Read one packed word using a machine index. -/
@[inline] def read (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (i : USize) (hi : i.toNat < n) : UInt64 :=
  let off := i * 8
  have ho : off.toNat = 8 * i.toNat := offset_toNat i hi hn
  have hp : (off + 4).toNat = off.toNat + 4 :=
    by simpa only [small 4 (by decide)] using
      add_toNat off 4 (by rw [ho, small 4 (by decide)]; omega)
  (a.val.bytes.ugetUInt32LE off (by rw [a.val.byteSize, a.property, ho]; omega)).toUInt64 |||
    ((a.val.bytes.ugetUInt32LE (off + 4) (by
      rw [a.val.byteSize, a.property, hp, ho]; omega)).toUInt64 <<< 32)

/-- Store one packed word using a machine index. -/
@[inline] def write (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (i : USize) (hi : i.toNat < n) (v : UInt64) : BF64.Packed.Buffer n :=
  let off := i * 8
  have ho : off.toNat = 8 * i.toNat := offset_toNat i hi hn
  have hp : (off + 4).toNat = off.toNat + 4 :=
    by simpa only [small 4 (by decide)] using
      add_toNat off 4 (by rw [ho, small 4 (by decide)]; omega)
  let b := a.val.bytes.usetUInt32LE off v.toUInt32
    (by rw [a.val.byteSize, a.property, ho]; omega)
  let c := b.usetUInt32LE (off + 4) (v >>> 32).toUInt32 (by
    simp only [b, ByteArray.size_usetUInt32LE, hp, ho, a.val.byteSize, a.property]; omega)
  ⟨⟨a.val.size, c, by simp only [c, b, ByteArray.size_usetUInt32LE, a.val.byteSize]⟩, a.property⟩

/-- Native reads agree with the certified packed word accessor. -/
theorem read_eq (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (i : USize) (hi : i.toNat < n) :
    read a hn i hi = (BF64.Packed.read a ⟨i.toNat, hi⟩).val := by
  simp only [read, BF64.Packed.read, BF64.Packed.get, ByteArray.ugetUInt32LE,
    ByteArray.getUInt32LE, offset_toNat i hi hn, add_toNat _ 4 (by
      rw [offset_toNat i hi hn, small 4 (by decide)]; omega), small 4 (by decide)]

/-- Native stores agree with the certified packed word accessor. -/
theorem write_eq (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (i : USize) (hi : i.toNat < n) (v : UInt64) :
    write a hn i hi v = BF64.Packed.write a ⟨i.toNat, hi⟩ ⟨v⟩ := by
  rcases a with ⟨⟨sz, bytes, hbytes⟩, hs⟩
  change sz = n at hs
  subst sz
  simp only [write, BF64.Packed.write, BF64.Packed.set, ByteArray.usetUInt32LE,
    offset_toNat i hi hn, add_toNat _ 4 (by
      rw [offset_toNat i hi hn, small 4 (by decide)]; omega), small 4 (by decide)]

/-- An exact machine representation of a small index. -/
theorem ofNat_toNat (i : Nat) (hi : i < 4294967296) :
    (USize.ofNat i).toNat = i := USize.toNat_ofNat_of_lt' (lt_of_lt_of_le hi USize.le_size)

/-- A checked offset inside a row of sixty-four planes. -/
theorem row_offset (base : USize) (hbase : base.toNat + 64 ≤ n)
    (hn : 8 * n < 4294967296) (i : Fin 64) :
    (base + USize.ofNat i.val).toNat < n := by
  rw [add_toNat _ _ (by rw [ofNat_toNat i.val (by have := i.isLt; omega)]; omega),
    ofNat_toNat i.val (by have := i.isLt; omega)]
  have := i.isLt
  omega

/-- Load a complete plane row with checked machine offsets. -/
@[noinline] def load (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (base : USize) (hbase : base.toNat + 64 ≤ n) : Block :=
  ⟨read a hn (base + 0) (by exact row_offset base hbase hn ⟨0, by decide⟩),
    read a hn (base + 1) (by exact row_offset base hbase hn ⟨1, by decide⟩),
    read a hn (base + 2) (by exact row_offset base hbase hn ⟨2, by decide⟩),
    read a hn (base + 3) (by exact row_offset base hbase hn ⟨3, by decide⟩),
    read a hn (base + 4) (by exact row_offset base hbase hn ⟨4, by decide⟩),
    read a hn (base + 5) (by exact row_offset base hbase hn ⟨5, by decide⟩),
    read a hn (base + 6) (by exact row_offset base hbase hn ⟨6, by decide⟩),
    read a hn (base + 7) (by exact row_offset base hbase hn ⟨7, by decide⟩),
    read a hn (base + 8) (by exact row_offset base hbase hn ⟨8, by decide⟩),
    read a hn (base + 9) (by exact row_offset base hbase hn ⟨9, by decide⟩),
    read a hn (base + 10) (by exact row_offset base hbase hn ⟨10, by decide⟩),
    read a hn (base + 11) (by exact row_offset base hbase hn ⟨11, by decide⟩),
    read a hn (base + 12) (by exact row_offset base hbase hn ⟨12, by decide⟩),
    read a hn (base + 13) (by exact row_offset base hbase hn ⟨13, by decide⟩),
    read a hn (base + 14) (by exact row_offset base hbase hn ⟨14, by decide⟩),
    read a hn (base + 15) (by exact row_offset base hbase hn ⟨15, by decide⟩),
    read a hn (base + 16) (by exact row_offset base hbase hn ⟨16, by decide⟩),
    read a hn (base + 17) (by exact row_offset base hbase hn ⟨17, by decide⟩),
    read a hn (base + 18) (by exact row_offset base hbase hn ⟨18, by decide⟩),
    read a hn (base + 19) (by exact row_offset base hbase hn ⟨19, by decide⟩),
    read a hn (base + 20) (by exact row_offset base hbase hn ⟨20, by decide⟩),
    read a hn (base + 21) (by exact row_offset base hbase hn ⟨21, by decide⟩),
    read a hn (base + 22) (by exact row_offset base hbase hn ⟨22, by decide⟩),
    read a hn (base + 23) (by exact row_offset base hbase hn ⟨23, by decide⟩),
    read a hn (base + 24) (by exact row_offset base hbase hn ⟨24, by decide⟩),
    read a hn (base + 25) (by exact row_offset base hbase hn ⟨25, by decide⟩),
    read a hn (base + 26) (by exact row_offset base hbase hn ⟨26, by decide⟩),
    read a hn (base + 27) (by exact row_offset base hbase hn ⟨27, by decide⟩),
    read a hn (base + 28) (by exact row_offset base hbase hn ⟨28, by decide⟩),
    read a hn (base + 29) (by exact row_offset base hbase hn ⟨29, by decide⟩),
    read a hn (base + 30) (by exact row_offset base hbase hn ⟨30, by decide⟩),
    read a hn (base + 31) (by exact row_offset base hbase hn ⟨31, by decide⟩),
    read a hn (base + 32) (by exact row_offset base hbase hn ⟨32, by decide⟩),
    read a hn (base + 33) (by exact row_offset base hbase hn ⟨33, by decide⟩),
    read a hn (base + 34) (by exact row_offset base hbase hn ⟨34, by decide⟩),
    read a hn (base + 35) (by exact row_offset base hbase hn ⟨35, by decide⟩),
    read a hn (base + 36) (by exact row_offset base hbase hn ⟨36, by decide⟩),
    read a hn (base + 37) (by exact row_offset base hbase hn ⟨37, by decide⟩),
    read a hn (base + 38) (by exact row_offset base hbase hn ⟨38, by decide⟩),
    read a hn (base + 39) (by exact row_offset base hbase hn ⟨39, by decide⟩),
    read a hn (base + 40) (by exact row_offset base hbase hn ⟨40, by decide⟩),
    read a hn (base + 41) (by exact row_offset base hbase hn ⟨41, by decide⟩),
    read a hn (base + 42) (by exact row_offset base hbase hn ⟨42, by decide⟩),
    read a hn (base + 43) (by exact row_offset base hbase hn ⟨43, by decide⟩),
    read a hn (base + 44) (by exact row_offset base hbase hn ⟨44, by decide⟩),
    read a hn (base + 45) (by exact row_offset base hbase hn ⟨45, by decide⟩),
    read a hn (base + 46) (by exact row_offset base hbase hn ⟨46, by decide⟩),
    read a hn (base + 47) (by exact row_offset base hbase hn ⟨47, by decide⟩),
    read a hn (base + 48) (by exact row_offset base hbase hn ⟨48, by decide⟩),
    read a hn (base + 49) (by exact row_offset base hbase hn ⟨49, by decide⟩),
    read a hn (base + 50) (by exact row_offset base hbase hn ⟨50, by decide⟩),
    read a hn (base + 51) (by exact row_offset base hbase hn ⟨51, by decide⟩),
    read a hn (base + 52) (by exact row_offset base hbase hn ⟨52, by decide⟩),
    read a hn (base + 53) (by exact row_offset base hbase hn ⟨53, by decide⟩),
    read a hn (base + 54) (by exact row_offset base hbase hn ⟨54, by decide⟩),
    read a hn (base + 55) (by exact row_offset base hbase hn ⟨55, by decide⟩),
    read a hn (base + 56) (by exact row_offset base hbase hn ⟨56, by decide⟩),
    read a hn (base + 57) (by exact row_offset base hbase hn ⟨57, by decide⟩),
    read a hn (base + 58) (by exact row_offset base hbase hn ⟨58, by decide⟩),
    read a hn (base + 59) (by exact row_offset base hbase hn ⟨59, by decide⟩),
    read a hn (base + 60) (by exact row_offset base hbase hn ⟨60, by decide⟩),
    read a hn (base + 61) (by exact row_offset base hbase hn ⟨61, by decide⟩),
    read a hn (base + 62) (by exact row_offset base hbase hn ⟨62, by decide⟩),
    read a hn (base + 63) (by exact row_offset base hbase hn ⟨63, by decide⟩)⟩

/-- Store a complete plane row with checked machine offsets. -/
@[noinline] def store (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (base : USize) (hbase : base.toNat + 64 ≤ n) (v : Block) : BF64.Packed.Buffer n :=
  let a := write a hn (base + 0) (by exact row_offset base hbase hn ⟨0, by decide⟩) v.w0
  let a := write a hn (base + 1) (by exact row_offset base hbase hn ⟨1, by decide⟩) v.w1
  let a := write a hn (base + 2) (by exact row_offset base hbase hn ⟨2, by decide⟩) v.w2
  let a := write a hn (base + 3) (by exact row_offset base hbase hn ⟨3, by decide⟩) v.w3
  let a := write a hn (base + 4) (by exact row_offset base hbase hn ⟨4, by decide⟩) v.w4
  let a := write a hn (base + 5) (by exact row_offset base hbase hn ⟨5, by decide⟩) v.w5
  let a := write a hn (base + 6) (by exact row_offset base hbase hn ⟨6, by decide⟩) v.w6
  let a := write a hn (base + 7) (by exact row_offset base hbase hn ⟨7, by decide⟩) v.w7
  let a := write a hn (base + 8) (by exact row_offset base hbase hn ⟨8, by decide⟩) v.w8
  let a := write a hn (base + 9) (by exact row_offset base hbase hn ⟨9, by decide⟩) v.w9
  let a := write a hn (base + 10) (by exact row_offset base hbase hn ⟨10, by decide⟩) v.w10
  let a := write a hn (base + 11) (by exact row_offset base hbase hn ⟨11, by decide⟩) v.w11
  let a := write a hn (base + 12) (by exact row_offset base hbase hn ⟨12, by decide⟩) v.w12
  let a := write a hn (base + 13) (by exact row_offset base hbase hn ⟨13, by decide⟩) v.w13
  let a := write a hn (base + 14) (by exact row_offset base hbase hn ⟨14, by decide⟩) v.w14
  let a := write a hn (base + 15) (by exact row_offset base hbase hn ⟨15, by decide⟩) v.w15
  let a := write a hn (base + 16) (by exact row_offset base hbase hn ⟨16, by decide⟩) v.w16
  let a := write a hn (base + 17) (by exact row_offset base hbase hn ⟨17, by decide⟩) v.w17
  let a := write a hn (base + 18) (by exact row_offset base hbase hn ⟨18, by decide⟩) v.w18
  let a := write a hn (base + 19) (by exact row_offset base hbase hn ⟨19, by decide⟩) v.w19
  let a := write a hn (base + 20) (by exact row_offset base hbase hn ⟨20, by decide⟩) v.w20
  let a := write a hn (base + 21) (by exact row_offset base hbase hn ⟨21, by decide⟩) v.w21
  let a := write a hn (base + 22) (by exact row_offset base hbase hn ⟨22, by decide⟩) v.w22
  let a := write a hn (base + 23) (by exact row_offset base hbase hn ⟨23, by decide⟩) v.w23
  let a := write a hn (base + 24) (by exact row_offset base hbase hn ⟨24, by decide⟩) v.w24
  let a := write a hn (base + 25) (by exact row_offset base hbase hn ⟨25, by decide⟩) v.w25
  let a := write a hn (base + 26) (by exact row_offset base hbase hn ⟨26, by decide⟩) v.w26
  let a := write a hn (base + 27) (by exact row_offset base hbase hn ⟨27, by decide⟩) v.w27
  let a := write a hn (base + 28) (by exact row_offset base hbase hn ⟨28, by decide⟩) v.w28
  let a := write a hn (base + 29) (by exact row_offset base hbase hn ⟨29, by decide⟩) v.w29
  let a := write a hn (base + 30) (by exact row_offset base hbase hn ⟨30, by decide⟩) v.w30
  let a := write a hn (base + 31) (by exact row_offset base hbase hn ⟨31, by decide⟩) v.w31
  let a := write a hn (base + 32) (by exact row_offset base hbase hn ⟨32, by decide⟩) v.w32
  let a := write a hn (base + 33) (by exact row_offset base hbase hn ⟨33, by decide⟩) v.w33
  let a := write a hn (base + 34) (by exact row_offset base hbase hn ⟨34, by decide⟩) v.w34
  let a := write a hn (base + 35) (by exact row_offset base hbase hn ⟨35, by decide⟩) v.w35
  let a := write a hn (base + 36) (by exact row_offset base hbase hn ⟨36, by decide⟩) v.w36
  let a := write a hn (base + 37) (by exact row_offset base hbase hn ⟨37, by decide⟩) v.w37
  let a := write a hn (base + 38) (by exact row_offset base hbase hn ⟨38, by decide⟩) v.w38
  let a := write a hn (base + 39) (by exact row_offset base hbase hn ⟨39, by decide⟩) v.w39
  let a := write a hn (base + 40) (by exact row_offset base hbase hn ⟨40, by decide⟩) v.w40
  let a := write a hn (base + 41) (by exact row_offset base hbase hn ⟨41, by decide⟩) v.w41
  let a := write a hn (base + 42) (by exact row_offset base hbase hn ⟨42, by decide⟩) v.w42
  let a := write a hn (base + 43) (by exact row_offset base hbase hn ⟨43, by decide⟩) v.w43
  let a := write a hn (base + 44) (by exact row_offset base hbase hn ⟨44, by decide⟩) v.w44
  let a := write a hn (base + 45) (by exact row_offset base hbase hn ⟨45, by decide⟩) v.w45
  let a := write a hn (base + 46) (by exact row_offset base hbase hn ⟨46, by decide⟩) v.w46
  let a := write a hn (base + 47) (by exact row_offset base hbase hn ⟨47, by decide⟩) v.w47
  let a := write a hn (base + 48) (by exact row_offset base hbase hn ⟨48, by decide⟩) v.w48
  let a := write a hn (base + 49) (by exact row_offset base hbase hn ⟨49, by decide⟩) v.w49
  let a := write a hn (base + 50) (by exact row_offset base hbase hn ⟨50, by decide⟩) v.w50
  let a := write a hn (base + 51) (by exact row_offset base hbase hn ⟨51, by decide⟩) v.w51
  let a := write a hn (base + 52) (by exact row_offset base hbase hn ⟨52, by decide⟩) v.w52
  let a := write a hn (base + 53) (by exact row_offset base hbase hn ⟨53, by decide⟩) v.w53
  let a := write a hn (base + 54) (by exact row_offset base hbase hn ⟨54, by decide⟩) v.w54
  let a := write a hn (base + 55) (by exact row_offset base hbase hn ⟨55, by decide⟩) v.w55
  let a := write a hn (base + 56) (by exact row_offset base hbase hn ⟨56, by decide⟩) v.w56
  let a := write a hn (base + 57) (by exact row_offset base hbase hn ⟨57, by decide⟩) v.w57
  let a := write a hn (base + 58) (by exact row_offset base hbase hn ⟨58, by decide⟩) v.w58
  let a := write a hn (base + 59) (by exact row_offset base hbase hn ⟨59, by decide⟩) v.w59
  let a := write a hn (base + 60) (by exact row_offset base hbase hn ⟨60, by decide⟩) v.w60
  let a := write a hn (base + 61) (by exact row_offset base hbase hn ⟨61, by decide⟩) v.w61
  let a := write a hn (base + 62) (by exact row_offset base hbase hn ⟨62, by decide⟩) v.w62
  let a := write a hn (base + 63) (by exact row_offset base hbase hn ⟨63, by decide⟩) v.w63
  a

end Native
end AdditiveNTT.Bitsliced
