/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Block

/-! # Packed scratch tables for four-bit binary linear maps -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace AdditiveNTT.Bitsliced

/-- Sixteen groups of sixteen little-endian words. -/
abbrev Scratch := {b : ByteArray // b.size = 2048}

private theorem small (n : Nat) (h : n < 4294967296) :
    (no_index (OfNat.ofNat n : USize)).toNat = n := by
  apply USize.toNat_ofNat_of_lt
  exact lt_of_lt_of_le h USize.le_size

private theorem plus4 (i : USize) (h : i.toNat ≤ 2040) :
    (i + 4).toNat = i.toNat + 4 := by
  rw [USize.toNat_add, small 4 (by decide), Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le (by omega) USize.le_size

/-- Read a scratch word at a checked machine byte offset. -/
@[inline] def Scratch.read (s : Scratch) (i : USize) (h : i.toNat ≤ 2040) : UInt64 :=
  (s.val.ugetUInt32LE i (by rw [s.property]; omega)).toUInt64 |||
    ((s.val.ugetUInt32LE (i + 4) (by rw [plus4 i h, s.property]; omega)).toUInt64 <<< 32)

/-- Overwrite one scratch word, reusing the byte buffer. -/
@[inline] def Scratch.write (s : Scratch) (i : USize) (h : i.toNat ≤ 2040)
    (v : UInt64) : Scratch :=
  let b := s.val.usetUInt32LE i v.toUInt32 (by rw [s.property]; omega)
  let c := b.usetUInt32LE (i + 4) (v >>> 32).toUInt32 (by
    simp only [b, ByteArray.size_usetUInt32LE, plus4 i h, s.property]; omega)
  ⟨c, by simp only [c, b, ByteArray.size_usetUInt32LE, s.property]⟩

/-- Byte offset of the selected four-bit linear combination. -/
@[inline] def nibbleOffset (g : USize) (v : UInt64) : USize :=
  g * 128 + (v &&& 15).toUSize * 8

theorem nibbleOffset_le (g : USize) (hg : g.toNat < 16) (v : UInt64) :
    (nibbleOffset g v).toNat ≤ 2040 := by
  have hv : (v &&& 15).toNat < 16 := by
    rw [UInt64.toNat_and]
    exact Nat.and_lt_two_pow _ (by decide : (15 : UInt64).toNat < 2 ^ 4)
  have hs : 4294967296 ≤ 2 ^ System.Platform.numBits := USize.le_size
  have hc : (v &&& 15).toUSize.toNat = (v &&& 15).toNat := by
    rw [UInt64.toNat_toUSize, Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) hs)]
  simp only [nibbleOffset, USize.toNat_add, USize.toNat_mul, small 128 (by decide),
    small 8 (by decide), hc]
  have h1 : g.toNat * 128 < 2 ^ System.Platform.numBits := lt_of_lt_of_le (by omega) hs
  have h2 : (v &&& 15).toNat * 8 < 2 ^ System.Platform.numBits :=
    lt_of_lt_of_le (by omega) hs
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) hs)]
  omega

/-- Apply one table group without a branch-based register selector. -/
@[inline] def Scratch.lookup (s : Scratch) (g : USize) (hg : g.toNat < 16)
    (v : UInt64) : UInt64 := s.read (nibbleOffset g v) (nibbleOffset_le g hg v)

/-- Fill a group of four-bit combinations at a checked machine group index. -/
@[inline] def fillChunk (s : Scratch) (g : USize) (hg : g.toNat < 16) (t : Chunk) : Scratch :=
  let s := s.write (nibbleOffset g 0) (nibbleOffset_le g hg 0) t.w0
  let s := s.write (nibbleOffset g 1) (nibbleOffset_le g hg 1) t.w1
  let s := s.write (nibbleOffset g 2) (nibbleOffset_le g hg 2) t.w2
  let s := s.write (nibbleOffset g 3) (nibbleOffset_le g hg 3) t.w3
  let s := s.write (nibbleOffset g 4) (nibbleOffset_le g hg 4) t.w4
  let s := s.write (nibbleOffset g 5) (nibbleOffset_le g hg 5) t.w5
  let s := s.write (nibbleOffset g 6) (nibbleOffset_le g hg 6) t.w6
  let s := s.write (nibbleOffset g 7) (nibbleOffset_le g hg 7) t.w7
  let s := s.write (nibbleOffset g 8) (nibbleOffset_le g hg 8) t.w8
  let s := s.write (nibbleOffset g 9) (nibbleOffset_le g hg 9) t.w9
  let s := s.write (nibbleOffset g 10) (nibbleOffset_le g hg 10) t.w10
  let s := s.write (nibbleOffset g 11) (nibbleOffset_le g hg 11) t.w11
  let s := s.write (nibbleOffset g 12) (nibbleOffset_le g hg 12) t.w12
  let s := s.write (nibbleOffset g 13) (nibbleOffset_le g hg 13) t.w13
  let s := s.write (nibbleOffset g 14) (nibbleOffset_le g hg 14) t.w14
  let s := s.write (nibbleOffset g 15) (nibbleOffset_le g hg 15) t.w15
  s

/-- Fill all four-bit XOR combinations of the input planes in reusable storage. -/
@[noinline] def prepareScratch (s : Scratch) (a : Block) : Scratch :=
  let s := fillChunk s 0 (by rw [small 0 (by decide)]; decide)
    (Chunk.create a.w0 a.w1 a.w2 a.w3)
  let s := fillChunk s 1 (by rw [small 1 (by decide)]; decide)
    (Chunk.create a.w4 a.w5 a.w6 a.w7)
  let s := fillChunk s 2 (by rw [small 2 (by decide)]; decide)
    (Chunk.create a.w8 a.w9 a.w10 a.w11)
  let s := fillChunk s 3 (by rw [small 3 (by decide)]; decide)
    (Chunk.create a.w12 a.w13 a.w14 a.w15)
  let s := fillChunk s 4 (by rw [small 4 (by decide)]; decide)
    (Chunk.create a.w16 a.w17 a.w18 a.w19)
  let s := fillChunk s 5 (by rw [small 5 (by decide)]; decide)
    (Chunk.create a.w20 a.w21 a.w22 a.w23)
  let s := fillChunk s 6 (by rw [small 6 (by decide)]; decide)
    (Chunk.create a.w24 a.w25 a.w26 a.w27)
  let s := fillChunk s 7 (by rw [small 7 (by decide)]; decide)
    (Chunk.create a.w28 a.w29 a.w30 a.w31)
  let s := fillChunk s 8 (by rw [small 8 (by decide)]; decide)
    (Chunk.create a.w32 a.w33 a.w34 a.w35)
  let s := fillChunk s 9 (by rw [small 9 (by decide)]; decide)
    (Chunk.create a.w36 a.w37 a.w38 a.w39)
  let s := fillChunk s 10 (by rw [small 10 (by decide)]; decide)
    (Chunk.create a.w40 a.w41 a.w42 a.w43)
  let s := fillChunk s 11 (by rw [small 11 (by decide)]; decide)
    (Chunk.create a.w44 a.w45 a.w46 a.w47)
  let s := fillChunk s 12 (by rw [small 12 (by decide)]; decide)
    (Chunk.create a.w48 a.w49 a.w50 a.w51)
  let s := fillChunk s 13 (by rw [small 13 (by decide)]; decide)
    (Chunk.create a.w52 a.w53 a.w54 a.w55)
  let s := fillChunk s 14 (by rw [small 14 (by decide)]; decide)
    (Chunk.create a.w56 a.w57 a.w58 a.w59)
  let s := fillChunk s 15 (by rw [small 15 (by decide)]; decide)
    (Chunk.create a.w60 a.w61 a.w62 a.w63)
  s

/-- Evaluate one binary row with sixteen packed lookups. -/
@[noinline] def dotScratch (s : @& Scratch) (m : UInt64) : UInt64 :=
  s.lookup 0 (by exact (small 0 (by decide)).trans_lt (by decide)) (m >>> 0) ^^^
    s.lookup 1 (by exact (small 1 (by decide)).trans_lt (by decide)) (m >>> 4) ^^^
    s.lookup 2 (by exact (small 2 (by decide)).trans_lt (by decide)) (m >>> 8) ^^^
    s.lookup 3 (by exact (small 3 (by decide)).trans_lt (by decide)) (m >>> 12) ^^^
    s.lookup 4 (by exact (small 4 (by decide)).trans_lt (by decide)) (m >>> 16) ^^^
    s.lookup 5 (by exact (small 5 (by decide)).trans_lt (by decide)) (m >>> 20) ^^^
    s.lookup 6 (by exact (small 6 (by decide)).trans_lt (by decide)) (m >>> 24) ^^^
    s.lookup 7 (by exact (small 7 (by decide)).trans_lt (by decide)) (m >>> 28) ^^^
    s.lookup 8 (by exact (small 8 (by decide)).trans_lt (by decide)) (m >>> 32) ^^^
    s.lookup 9 (by exact (small 9 (by decide)).trans_lt (by decide)) (m >>> 36) ^^^
    s.lookup 10 (by exact (small 10 (by decide)).trans_lt (by decide)) (m >>> 40) ^^^
    s.lookup 11 (by exact (small 11 (by decide)).trans_lt (by decide)) (m >>> 44) ^^^
    s.lookup 12 (by exact (small 12 (by decide)).trans_lt (by decide)) (m >>> 48) ^^^
    s.lookup 13 (by exact (small 13 (by decide)).trans_lt (by decide)) (m >>> 52) ^^^
    s.lookup 14 (by exact (small 14 (by decide)).trans_lt (by decide)) (m >>> 56) ^^^
    s.lookup 15 (by exact (small 15 (by decide)).trans_lt (by decide)) (m >>> 60)

/-- Evaluate all sixty-four matrix rows using packed four-bit tables. -/
@[noinline] def applyScratch (s : @& Scratch) (m : @& Block) : Block :=
  ⟨dotScratch s m.w0,
    dotScratch s m.w1,
    dotScratch s m.w2,
    dotScratch s m.w3,
    dotScratch s m.w4,
    dotScratch s m.w5,
    dotScratch s m.w6,
    dotScratch s m.w7,
    dotScratch s m.w8,
    dotScratch s m.w9,
    dotScratch s m.w10,
    dotScratch s m.w11,
    dotScratch s m.w12,
    dotScratch s m.w13,
    dotScratch s m.w14,
    dotScratch s m.w15,
    dotScratch s m.w16,
    dotScratch s m.w17,
    dotScratch s m.w18,
    dotScratch s m.w19,
    dotScratch s m.w20,
    dotScratch s m.w21,
    dotScratch s m.w22,
    dotScratch s m.w23,
    dotScratch s m.w24,
    dotScratch s m.w25,
    dotScratch s m.w26,
    dotScratch s m.w27,
    dotScratch s m.w28,
    dotScratch s m.w29,
    dotScratch s m.w30,
    dotScratch s m.w31,
    dotScratch s m.w32,
    dotScratch s m.w33,
    dotScratch s m.w34,
    dotScratch s m.w35,
    dotScratch s m.w36,
    dotScratch s m.w37,
    dotScratch s m.w38,
    dotScratch s m.w39,
    dotScratch s m.w40,
    dotScratch s m.w41,
    dotScratch s m.w42,
    dotScratch s m.w43,
    dotScratch s m.w44,
    dotScratch s m.w45,
    dotScratch s m.w46,
    dotScratch s m.w47,
    dotScratch s m.w48,
    dotScratch s m.w49,
    dotScratch s m.w50,
    dotScratch s m.w51,
    dotScratch s m.w52,
    dotScratch s m.w53,
    dotScratch s m.w54,
    dotScratch s m.w55,
    dotScratch s m.w56,
    dotScratch s m.w57,
    dotScratch s m.w58,
    dotScratch s m.w59,
    dotScratch s m.w60,
    dotScratch s m.w61,
    dotScratch s m.w62,
    dotScratch s m.w63⟩

end AdditiveNTT.Bitsliced
