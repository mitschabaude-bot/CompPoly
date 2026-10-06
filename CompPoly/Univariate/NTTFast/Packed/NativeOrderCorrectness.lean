/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
import all CompPoly.Univariate.NTTFast.Packed.NativeOrder
public import CompPoly.Univariate.NTTFast.Packed.NativeOrder
public import CompPoly.Univariate.NTTFast.Packed.Rows
public import CompPoly.Univariate.NTTFast.Packed.Correctness
public import CompPoly.Univariate.NTTFast.Packed.SliceTreeCorrectness

/-! # Correctness of the parallel natural-order output

Every loop of `NativeOrder` appends sixteen words at a time. Their results are stated as
`rows`, a concatenation of sixteen-word literals with a single indexing lemma, so the
tile, leaf-reversal and join proofs reduce to index arithmetic.
-/

@[expose] public section
open CompPoly
namespace CompPoly.CPolynomial.NTTFast.Packed

namespace Native

open Storage

/-- Appending a sixteen-word literal. -/
theorem storeWords_lit16 (o : Array UInt32) (g : Nat → UInt32) :
    storeWords (pack o) 0 16 true (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8)
      (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15) = pack (o ++ lit16 g) := by
  rw [storeWords_append_pack o 0 16 (by decide)]
  rfl

/-- A checked read at a numeral offset inside a known word range. -/
theorem readRaw_pack_at (v : Array UInt32) (q : USize) (o : Nat) (ho : o < 16)
    (h : q.toNat + 16 ≤ v.size) (hs : (pack v).size < USize.size) :
    readRaw (pack v) q (OfNat.ofNat o) true (by intro h; cases h) = v.getD (q.toNat + o) 0 := by
  rw [readRaw_pack_true v q (OfNat.ofNat o)
    (by rw [usize_numeral o (by omega)]; refine ⟨?_, hs⟩; rw [size_pack]; omega),
    usize_numeral o (by omega)]

/-- One aligned line of a packed word array. -/
theorem line_pack (v : Array UInt32) (q : USize) (h : q.toNat + 16 ≤ v.size)
    (hs : (pack v).size < USize.size) :
    line (pack v) q = ⟨v.getD (q.toNat + 0) 0, v.getD (q.toNat + 1) 0, v.getD (q.toNat + 2) 0,
      v.getD (q.toNat + 3) 0, v.getD (q.toNat + 4) 0, v.getD (q.toNat + 5) 0,
      v.getD (q.toNat + 6) 0, v.getD (q.toNat + 7) 0, v.getD (q.toNat + 8) 0,
      v.getD (q.toNat + 9) 0, v.getD (q.toNat + 10) 0, v.getD (q.toNat + 11) 0,
      v.getD (q.toNat + 12) 0, v.getD (q.toNat + 13) 0, v.getD (q.toNat + 14) 0,
      v.getD (q.toNat + 15) 0⟩ := by
  unfold line
  rw [readRaw_pack_at v q 0 (by decide) h hs, readRaw_pack_at v q 1 (by decide) h hs,
    readRaw_pack_at v q 2 (by decide) h hs, readRaw_pack_at v q 3 (by decide) h hs,
    readRaw_pack_at v q 4 (by decide) h hs, readRaw_pack_at v q 5 (by decide) h hs,
    readRaw_pack_at v q 6 (by decide) h hs, readRaw_pack_at v q 7 (by decide) h hs,
    readRaw_pack_at v q 8 (by decide) h hs, readRaw_pack_at v q 9 (by decide) h hs,
    readRaw_pack_at v q 10 (by decide) h hs, readRaw_pack_at v q 11 (by decide) h hs,
    readRaw_pack_at v q 12 (by decide) h hs, readRaw_pack_at v q 13 (by decide) h hs,
    readRaw_pack_at v q 14 (by decide) h hs, readRaw_pack_at v q 15 (by decide) h hs]

/-- The `c`-th of sixteen word arrays. -/
def sel16 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Array UInt32) (c : Nat) :
    Array UInt32 :=
  #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15].getD c #[]

/-- A sixteen-element literal is its own leading segment. -/
theorem extract_literal16 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32) :
    (#[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] : Array UInt32).extract
      0 16 = #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] :=
  Array.extract_size

/-- One transposed tile appends rows `q, …, q + 15` of the sixteen-stream interleave. -/
theorem transposeStep_pack (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 o : Array UInt32)
    (q : USize)
    (h : ∀ c < 16, q.toNat + 16 ≤
      (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c).size)
    (hs : ∀ c < 16,
      (pack (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c)).size < USize.size) :
    transposeStep (pack v0) (pack v1) (pack v2) (pack v3) (pack v4) (pack v5) (pack v6)
      (pack v7) (pack v8) (pack v9) (pack v10) (pack v11) (pack v12) (pack v13) (pack v14)
      (pack v15) q (pack o) =
      pack (o ++ rows (fun u c ↦
        (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c).getD (q.toNat + u) 0)
        16) := by
  unfold transposeStep
  rw [
    line_pack v0 q (h 0 (by decide)) (hs 0 (by decide)),
    line_pack v1 q (h 1 (by decide)) (hs 1 (by decide)),
    line_pack v2 q (h 2 (by decide)) (hs 2 (by decide)),
    line_pack v3 q (h 3 (by decide)) (hs 3 (by decide)),
    line_pack v4 q (h 4 (by decide)) (hs 4 (by decide)),
    line_pack v5 q (h 5 (by decide)) (hs 5 (by decide)),
    line_pack v6 q (h 6 (by decide)) (hs 6 (by decide)),
    line_pack v7 q (h 7 (by decide)) (hs 7 (by decide)),
    line_pack v8 q (h 8 (by decide)) (hs 8 (by decide)),
    line_pack v9 q (h 9 (by decide)) (hs 9 (by decide)),
    line_pack v10 q (h 10 (by decide)) (hs 10 (by decide)),
    line_pack v11 q (h 11 (by decide)) (hs 11 (by decide)),
    line_pack v12 q (h 12 (by decide)) (hs 12 (by decide)),
    line_pack v13 q (h 13 (by decide)) (hs 13 (by decide)),
    line_pack v14 q (h 14 (by decide)) (hs 14 (by decide)),
    line_pack v15 q (h 15 (by decide)) (hs 15 (by decide))]
  simp only [storeWords_append_pack _ 0 16 (by decide), extract_literal16,
    show (16 : UInt8).toNat = 16 from rfl]
  simp only [rows, lit16, Array.append_assoc, Array.empty_append]
  rfl

/-- Adding a small numeral to a machine index that cannot wrap. -/
theorem usize_add_numeral (q : USize) (k : Nat) (hk : k < 4294967296)
    (h : q.toNat + k < USize.size) : (q + OfNat.ofNat k).toNat = q.toNat + k := by
  rw [USize.toNat_add, usize_numeral k hk, Nat.mod_eq_of_lt h]

/-- Repeated transposed tiles append consecutive interleave rows. -/
theorem transposeGo_pack (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Array UInt32)
    (count : Nat) (q : USize) (o : Array UInt32)
    (h : ∀ c < 16, q.toNat + 16 * count ≤
      (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c).size)
    (hs : ∀ c < 16,
      (pack (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c)).size < USize.size) :
    transposeGo (pack v0) (pack v1) (pack v2) (pack v3) (pack v4) (pack v5) (pack v6) (pack v7)
      (pack v8) (pack v9) (pack v10) (pack v11) (pack v12) (pack v13) (pack v14) (pack v15)
      count q (pack o) =
      pack (o ++ rows (fun u c ↦
        (sel16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 c).getD (q.toNat + u) 0)
        (16 * count)) := by
  induction count generalizing q o with
  | zero => simp only [transposeGo, rows, Array.append_empty]
  | succ count ih =>
    have hq : q.toNat + 16 < USize.size := by
      have h0 := h 0 (by decide)
      have hs0 := hs 0 (by decide)
      rw [size_pack] at hs0
      omega
    rw [transposeGo, transposeStep_pack v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 o q
        (fun c hc ↦ by have := h c hc; omega) hs,
      ih (q + 16) _
        (fun c hc ↦ by rw [usize_add_numeral q 16 (by decide) hq]; have := h c hc; omega),
      show 16 * (count + 1) = 16 + 16 * count by omega, rows_add, Array.append_assoc,
      usize_add_numeral q 16 (by decide) hq]
    simp only [Nat.add_assoc]

/-- A reversed leaf word reads the bit-reversed position and applies the optional scaling. -/
theorem revWord_pack (w : Array UInt32) (base p : USize) (m : Nat) (f : UInt32) (sc : Bool)
    (hm : m ≤ 32) (hp : p.toNat < 2 ^ m) (hb : base.toNat + 2 ^ m ≤ w.size)
    (hs : (pack w).size < USize.size) :
    revWord (pack w) base (32 - m).toUInt32 f sc p =
      scaleWord f sc (w.getD (base.toNat + NTT.Transform.bitRevNat m p.toNat) 0) := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hq : p.toUInt32 = p.toNat.toUInt32 := UInt32.toFin_inj.mp rfl
  have hr := reverse_index m p.toNat hm hp
  have hlt := NTT.Transform.bitRevNat_lt m p.toNat
  rw [size_pack] at hs
  have hx : (base + (reverse32 p.toNat.toUInt32 >>> (32 - m).toUInt32).toUSize).toNat =
      base.toNat + NTT.Transform.bitRevNat m p.toNat := by
    rw [USize.toNat_add, UInt32.toNat_toUSize, hr]
    exact Nat.mod_eq_of_lt (by omega)
  unfold revWord
  rw [hq, readWord_eq_read, hx, read_pack w _ (by rw [size_pack]; omega) (by omega)]

/-- `revWord_pack` at a numeral offset from a machine index. -/
theorem revWord_pack_add (w : Array UInt32) (base q : USize) (m : Nat) (f : UInt32) (sc : Bool)
    (k : Nat) (hk : k < 16) (hm : m ≤ 32) (hq : q.toNat + 16 ≤ 2 ^ m)
    (hb : base.toNat + 2 ^ m ≤ w.size) (hs : (pack w).size < USize.size) :
    revWord (pack w) base (32 - m).toUInt32 f sc (q + OfNat.ofNat k) =
      scaleWord f sc (w.getD (base.toNat + NTT.Transform.bitRevNat m (q.toNat + k)) 0) := by
  have hsz := hs
  rw [size_pack] at hsz
  have hp : (q + OfNat.ofNat k).toNat = q.toNat + k :=
    usize_add_numeral q k (by omega) (by omega)
  rw [revWord_pack w base _ m f sc hm (by omega) hb hs, hp]

/-- One reversal step appends sixteen consecutive locally reversed words. -/
theorem leafRevStep_pack (w o : Array UInt32) (base q : USize) (m : Nat) (f : UInt32) (sc : Bool)
    (hm : m ≤ 32) (hq : q.toNat + 16 ≤ 2 ^ m) (hb : base.toNat + 2 ^ m ≤ w.size)
    (hs : (pack w).size < USize.size) :
    leafRevStep (pack w) base (32 - m).toUInt32 f sc q (pack o) = pack (o ++ lit16 (fun u ↦
      scaleWord f sc (w.getD (base.toNat + NTT.Transform.bitRevNat m (q.toNat + u)) 0))) := by
  unfold leafRevStep
  rw [revWord_pack w base q m f sc hm (by omega) hb hs,
    revWord_pack_add w base q m f sc 1 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 2 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 3 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 4 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 5 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 6 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 7 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 8 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 9 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 10 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 11 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 12 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 13 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 14 (by decide) hm hq hb hs,
    revWord_pack_add w base q m f sc 15 (by decide) hm hq hb hs]
  simp only [storeWords_append_pack _ 0 16 (by decide), extract_literal16,
    show (16 : UInt8).toNat = 16 from rfl]
  rfl

/-- Repeated reversal steps append consecutive locally reversed words. -/
theorem leafRevGo_pack (w : Array UInt32) (base : USize) (m : Nat) (f : UInt32) (sc : Bool)
    (hm : m ≤ 32) (hb : base.toNat + 2 ^ m ≤ w.size) (hs : (pack w).size < USize.size)
    (count : Nat) (q : USize) (o : Array UInt32) (hq : q.toNat + 16 * count ≤ 2 ^ m) :
    leafRevGo (pack w) base (32 - m).toUInt32 f sc count q (pack o) = pack (o ++ rows (fun j u ↦
      scaleWord f sc (w.getD (base.toNat + NTT.Transform.bitRevNat m (q.toNat + (16 * j + u))) 0))
      count) := by
  induction count generalizing q o with
  | zero => simp only [leafRevGo, rows, Array.append_empty]
  | succ count ih =>
    have hsz := hs
    rw [size_pack] at hsz
    have h16 : (q + 16).toNat = q.toNat + 16 := usize_add_numeral q 16 (by decide) (by omega)
    rw [leafRevGo, leafRevStep_pack w o base q m f sc hm (by omega) hb hs,
      ih (q + 16) _ (by rw [h16]; omega), Nat.add_comm count 1, rows_add, Array.append_assoc, h16]
    have e1 : rows (fun j u ↦ scaleWord f sc
        (w.getD (base.toNat + NTT.Transform.bitRevNat m (q.toNat + (16 * j + u))) 0)) 1 =
        lit16 (fun u ↦ scaleWord f sc
          (w.getD (base.toNat + NTT.Transform.bitRevNat m (q.toNat + u)) 0)) := by
      simp only [rows, Array.empty_append, Nat.mul_zero, Nat.zero_add]
    have e2 : (fun j u ↦ scaleWord f sc
        (w.getD (base.toNat + NTT.Transform.bitRevNat m (q.toNat + 16 + (16 * j + u))) 0)) =
        (fun j u ↦ scaleWord f sc
          (w.getD (base.toNat + NTT.Transform.bitRevNat m (q.toNat + (16 * (1 + j) + u))) 0)) := by
      funext j u
      rw [show q.toNat + 16 + (16 * j + u) = q.toNat + (16 * (1 + j) + u) by omega]
    rw [e1, e2]

/-- A complete reversed leaf: word `i` is leaf word `bitrev i`, optionally scaled. -/
theorem leafRev_pack (w : Array UInt32) (logM l : Nat) (f : UInt32) (sc : Bool)
    (hm : 4 ≤ logM) (h32 : logM ≤ 32) (hl : (l + 1) * 2 ^ logM ≤ w.size)
    (hs : (pack w).size < USize.size) :
    leafRev (pack w) logM l f sc = pack (rows (fun j u ↦
      scaleWord f sc (w.getD (l * 2 ^ logM + NTT.Transform.bitRevNat logM (16 * j + u)) 0))
      (2 ^ logM / 16)) := by
  have hsz := hs
  rw [size_pack] at hsz
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hlw : l * 2 ^ logM + 2 ^ logM ≤ w.size := by rw [← Nat.succ_mul]; exact hl
  have hbase : (l * 2 ^ logM).toUSize.toNat = l * 2 ^ logM :=
    USize.toNat_ofNat_of_lt' (lt_of_le_of_lt
      (by have := Nat.le_trans (Nat.le_add_right (l * 2 ^ logM) (2 ^ logM)) hlw; omega) hsz)
  have hdiv : 16 * (2 ^ logM / 16) = 2 ^ logM := by
    have : 16 ∣ 2 ^ logM := by
      rw [show logM = 4 + (logM - 4) by omega, Nat.pow_add]
      exact Nat.dvd_mul_right _ _
    omega
  unfold leafRev
  rw [emptyWithCapacity_eq_pack, leafRevGo_pack w _ logM f sc h32
    (by rw [hbase]; exact hlw) hs _ 0 #[]
    (by simp only [USize.toNat_zero, Nat.zero_add, hdiv, Nat.le_refl])]
  simp only [Array.empty_append, hbase, USize.toNat_zero, Nat.zero_add]

/-- The interleave streams are the reversed leaves in four-bit reversed order. -/
theorem sel16_bitRev (V : Nat → Array UInt32) (c : Nat) (hc : c < 16) :
    sel16 (V 0) (V 8) (V 4) (V 12) (V 2) (V 10) (V 6) (V 14) (V 1) (V 9) (V 5) (V 13) (V 3)
      (V 11) (V 7) (V 15) c = V (NTT.Transform.bitRevNat 4 c) := by
  interval_cases c <;> rfl

/-- One interleave block: rows `q` up to `q + 16 * count` of the sixteen reversed leaves. -/
theorem interleaveRange_pack (V : Nat → Array UInt32) (M q count : Nat)
    (hV : ∀ l < 16, (V l).size = M) (hq : q + 16 * count ≤ M) (hs : 4 * M < USize.size) :
    interleaveRange ((Array.range 16).map fun l ↦ pack (V l)) q count =
      pack (rows (fun u c ↦ (V (NTT.Transform.bitRevNat 4 c)).getD (q + u) 0) (16 * count)) := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hqu : q.toUSize.toNat = q := USize.toNat_ofNat_of_lt' (by omega)
  unfold interleaveRange
  simp only [getD_map_range _ 16 0 (by decide), getD_map_range _ 16 1 (by decide),
    getD_map_range _ 16 2 (by decide), getD_map_range _ 16 3 (by decide),
    getD_map_range _ 16 4 (by decide), getD_map_range _ 16 5 (by decide),
    getD_map_range _ 16 6 (by decide), getD_map_range _ 16 7 (by decide),
    getD_map_range _ 16 8 (by decide), getD_map_range _ 16 9 (by decide),
    getD_map_range _ 16 10 (by decide), getD_map_range _ 16 11 (by decide),
    getD_map_range _ 16 12 (by decide), getD_map_range _ 16 13 (by decide),
    getD_map_range _ 16 14 (by decide), getD_map_range _ 16 15 (by decide)]
  rw [emptyWithCapacity_eq_pack, transposeGo_pack (V 0) (V 8) (V 4) (V 12) (V 2) (V 10) (V 6)
    (V 14) (V 1) (V 9) (V 5) (V 13) (V 3) (V 11) (V 7) (V 15) count q.toUSize #[]
    (fun c hc ↦ by rw [sel16_bitRev V c hc, hqu, hV _ (NTT.Transform.bitRevNat_lt 4 c)]; exact hq)
    (fun c hc ↦ by
      rw [sel16_bitRev V c hc, size_pack, hV _ (NTT.Transform.bitRevNat_lt 4 c)]; exact hs),
    Array.empty_append, hqu]
  congr 1
  exact rows_congr _ _ _ (fun j c hc ↦ by rw [sel16_bitRev V c hc])

/-- Joining the interleave blocks in task order concatenates their rows. -/
theorem foldl_blocks (g : Nat → Nat → UInt32) (B : Nat → ByteArray) (count k : Nat)
    (o : Array UInt32)
    (hB : ∀ t < k, B t = pack (rows (fun u c ↦ g (16 * count * t + u) c) (16 * count))) :
    (Array.range k).foldl (fun acc t ↦ acc ++ B t) (pack o) =
      pack (o ++ rows g (16 * count * k)) := by
  induction k with
  | zero =>
    rw [show Array.range 0 = #[] from Array.eq_empty_of_size_eq_zero Array.size_range]
    simp only [Array.foldl_empty, Nat.mul_zero, rows, Array.append_empty]
  | succ k ih =>
    rw [Array.range_succ, Array.foldl_append, ih (fun t ht ↦ hB t (by omega))]
    have hs : (#[k] : Array Nat).foldl (fun acc t ↦ acc ++ B t)
        (pack (o ++ rows g (16 * count * k))) =
        pack (o ++ rows g (16 * count * k)) ++ B k := by simp
    rw [hs, hB k (by omega), ← pack_append, Nat.mul_succ, rows_add, Array.append_assoc]

/-- The parallel natural-order output reads the bit-reversed word of every index. -/
theorem natural_pack (w : Array UInt32) (logN : Nat) (f : UInt32) (sc : Bool)
    (h12 : 12 ≤ logN) (h32 : logN ≤ 32) (hw : w.size = 2 ^ logN)
    (hs : (pack w).size < USize.size) :
    natural (pack w) logN f sc = pack (Array.ofFn (n := 2 ^ logN) fun i ↦
      scaleWord f sc (w.getD (NTT.Transform.bitRevNat logN i) 0)) := by
  obtain ⟨m, rfl⟩ : ∃ m, logN = m + 4 := ⟨logN - 4, by omega⟩
  have hsub : m + 4 - 4 = m := by omega
  have hpow : 2 ^ (m + 4) = 16 * 2 ^ m := by rw [Nat.pow_add]; omega
  have hm8 : 2 ^ m = 256 * (2 ^ m / 256) := by
    have : 256 ∣ 2 ^ m := by
      rw [show m = 8 + (m - 8) by omega, Nat.pow_add]
      exact Nat.dvd_mul_right _ _
    omega
  have hsz := hs
  rw [size_pack, hw] at hsz
  let H : Nat → Nat → UInt32 := fun l i ↦
    scaleWord f sc (w.getD (l * 2 ^ m + NTT.Transform.bitRevNat m i) 0)
  let V : Nat → Array UInt32 := fun l ↦ rows (fun j u ↦ H l (16 * j + u)) (2 ^ m / 16)
  have hV : ∀ l < 16, (V l).size = 2 ^ m := by
    intro l _
    simp only [V, size_rows]
    omega
  have hVget : ∀ l i, i < 2 ^ m → (V l).getD i 0 = H l i := by
    intro l i hi
    simp only [V]
    rw [getD_rows _ _ _ (by omega)]
    simp only [H]
    congr 4
    omega
  have hleaf : ∀ l < 16, leafRev (pack w) m l f sc = pack (V l) := by
    intro l hl
    exact leafRev_pack w m l f sc (by omega) (by omega)
      (by rw [hw, hpow]; exact Nat.mul_le_mul_right _ hl) hs
  have hr : ((Array.range 16).map fun l ↦ Task.spawn fun _ ↦ leafRev (pack w) m l f sc).map
      Task.get = (Array.range 16).map fun l ↦ pack (V l) := by
    rw [Array.map_map]
    apply Array.map_congr_left
    intro l hl
    exact hleaf l (Array.mem_range.mp hl)
  simp only [natural, hsub]
  rw [hr, Array.foldl_map, emptyWithCapacity_eq_pack,
    foldl_blocks (fun u c ↦ (V (NTT.Transform.bitRevNat 4 c)).getD u 0) _ (2 ^ m / 256) 16 #[]
      (fun t ht ↦ by
        simp only [Task.spawn]
        rw [interleaveRange_pack V (2 ^ m) _ _ hV (by
          have := Nat.mul_le_mul_left (16 * (2 ^ m / 256)) (show t + 1 ≤ 16 by omega)
          rw [Nat.mul_add, Nat.mul_one] at this
          omega) (by omega)]),
    Array.empty_append]
  congr 1
  apply array_eq_of_getD _ _ 0 (by rw [size_rows, Array.size_ofFn, hpow]; omega)
  intro i
  by_cases hi : i < 2 ^ (m + 4)
  · rw [getD_rows _ _ _ (by omega), getD_ofFn_bounded _ _ hi,
      hVget _ _ (by omega)]
    simp only [H]
    have hc := bitRevNat_concat m 4 (i / 16) (i % 16) (Nat.mod_lt _ (by decide))
    rw [show 2 ^ 4 * (i / 16) + i % 16 = i by omega] at hc
    rw [hc, Nat.mul_comm (2 ^ m)]
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [size_rows]; omega),
      Array.getElem?_eq_none (by rw [Array.size_ofFn]; omega)]

/-- The sequential decoder stores every word, in order, into a correctly sized array. -/
theorem unpackGo_packFields (X : Array KoalaBear.Fast.Field) (n : USize) (hn : X.size = n.toNat)
    (hs : (packFields X).size < USize.size) :
    ∀ (d : Nat) (i : USize) (out : Array KoalaBear.Fast.Field), n.toNat - i.toNat = d →
      i.toNat ≤ n.toNat → out.size = n.toNat → (∀ k < i.toNat, out.getD k 0 = X.getD k 0) →
      unpackGo (packFields X) n i out = X := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  intro d
  induction d with
  | zero =>
    intro i out hd hi hout hk
    rw [unpackGo]
    have hn' : ¬i < n := by rw [USize.lt_iff_toNat_lt]; omega
    simp only [hn', ↓reduceDIte]
    apply array_eq_of_getD _ _ 0 (by omega)
    intro k
    by_cases hk' : k < i.toNat
    · exact hk k hk'
    · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  | succ d ih =>
    intro i out hd hi hout hk
    have hlt : i < n := by rw [USize.lt_iff_toNat_lt]; omega
    have hio : i.toNat < out.size := by omega
    have hnsz := n.toNat_lt_size
    have h1 : (i + 1).toNat = i.toNat + 1 := Plan.usize_add_one i (by omega)
    rw [unpackGo]
    simp only [hlt, hio, ↓reduceDIte]
    have hread : ofWord (readWord (packFields X) i) = X.getD i.toNat 0 := by
      rw [readWord_eq_read, read_packFields X _ hs (by omega), ofWord_val]
    rw [hread]
    apply ih (i + 1) _ (by omega) (by omega) (by simp only [Array.uset, Array.size_set]; exact hout)
    intro k hk1
    simp only [Array.uset, Array.getD_eq_getD_getElem?, Array.getElem?_set]
    split
    · rename_i he
      rw [← he, Option.getD_some]
    · rw [h1] at hk1
      have := hk k (by omega)
      simpa only [Array.getD_eq_getD_getElem?] using this

/-- Unpacking a packed field array restores it. -/
theorem unpack_packFields (X : Array KoalaBear.Fast.Field) (hs : (packFields X).size < USize.size) :
    unpack (packFields X) X.size = X := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hsz := hs
  rw [size_packFields] at hsz
  have hn : X.size.toUSize.toNat = X.size := USize.toNat_ofNat_of_lt' (by omega)
  unfold unpack
  exact unpackGo_packFields X _ hn.symm hs _ 0 _ rfl (by simp only [USize.toNat_zero]; omega)
    (by rw [Array.size_replicate, hn]) (fun k hk ↦ by simp only [USize.toNat_zero] at hk; omega)

/-- Natural-order output of a packed field array is its natural-order decoding. -/
theorem natural_packFields (S : Array KoalaBear.Fast.Field) (logN : Nat)
    (factor : KoalaBear.Fast.Field) (sc : Bool) (h12 : 12 ≤ logN) (h32 : logN ≤ 32)
    (hS : S.size = 2 ^ logN) (hs : (packFields S).size < USize.size) :
    natural (packFields S) logN factor.val sc = packFields (decodedFields logN S factor sc) := by
  unfold packFields
  rw [natural_pack _ logN _ sc h12 h32 (by rw [Array.size_map, hS]) hs]
  congr 1
  simp only [decodedFields, Array.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, getD_map_val, scaleWord]
  cases sc <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_val]

end Native
/-- The packed in/out pipeline computes the DFT with optional inverse normalization. -/
theorem Native.runPacked_dft (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (depth : Nat) (factor : KoalaBear.Fast.Field)
    (a : Array KoalaBear.Fast.Field) (inverse : Bool) (ht : TwiddlesFor D tw) (hs : a.size = D.n)
    (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) :
    Native.runPacked (tw.map packFields) D.logN depth factor.val (packFields a) inverse =
      packFields (if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
        else NTT.Forward.forwardSpec D a) := by
  let normalize := inverse && D.logN - depth ≥ 4 && (D.logN - depth) % 2 == 0
  have hn : ValidLeafNormalization D.logN depth normalize := by
    intro h
    simp only [normalize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.2, h.2⟩
  have hi : normalize = true → inverse = true := by
    intro h
    simp only [normalize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact h.1.1
  have hsize : (normalizedDifSpec D a factor normalize).size = 2 ^ D.logN :=
    size_normalizedDifSpec D a factor normalize
  have hpu : (packFields (normalizedDifSpec D a factor normalize)).size < USize.size := by
    rw [size_packFields, hsize]
    exact hu
  have hb : Native.assembleChunks (4 * 2 ^ D.logN)
      (Native.sliceChunks (tw.map packFields) D.logN #[packFields a] factor.val normalize
        (Native.sliceCount D.logN depth) depth).get =
          packFields (normalizedDifSpec D a factor normalize) := by
    rw [Native.assembleChunks_capacity, ← Native.slicesOf_one a D.n hs,
      Native.sliceChunks_assemble tw _ _ _ _ D.logN 1 D.n _ (Nat.one_mul _) (by decide)
        (TwiddlesFor.invariants D tw ht).1 hu]
    rw [Native.ofFn_getD a (2 ^ D.logN) hs, Native.splitChunks_eq,
      Native.splitTask_correct D tw a factor normalize depth ht hs hu hn]
  unfold Native.runPacked
  change (if Native.naturalShape D.logN depth then
    Native.natural (Native.assembleChunks (4 * 2 ^ D.logN) (Native.sliceChunks
      (tw.map packFields) D.logN #[packFields a] factor.val normalize
        (Native.sliceCount D.logN depth) depth).get) D.logN factor.val (inverse && !normalize)
    else Native.encode (Native.decodeTiled D.logN (Native.assembleChunks (4 * 2 ^ D.logN)
      (Native.sliceChunks (tw.map packFields) D.logN #[packFields a] factor.val normalize
        (Native.sliceCount D.logN depth) depth).get) factor.val (inverse && !normalize))) = _
  rw [hb]
  split
  · rename_i hshape
    simp only [Native.naturalShape, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hshape
    rw [Native.natural_packFields _ _ factor _ hshape.1.2 h32 hsize hpu,
      decodedFields_normalizedDifSpec D a factor normalize inverse hi]
  · rw [Native.decodeTiled_packFields _ _ factor _ h32 hsize hpu, Native.encode_eq,
      decodedFields_normalizedDifSpec D a factor normalize inverse hi]

/-- The field-array pipeline computes the DFT with optional inverse normalization. -/
theorem Native.runFields_dft (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (depth : Nat) (factor : KoalaBear.Fast.Field)
    (a : Array KoalaBear.Fast.Field) (inverse : Bool) (ht : TwiddlesFor D tw) (hs : a.size = D.n)
    (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) :
    Native.runFields (tw.map packFields) D.logN depth factor.val a inverse =
      if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
      else NTT.Forward.forwardSpec D a := by
  unfold Native.runFields
  split
  · rename_i hshape
    simp only [Native.naturalShape, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hshape
    let normalize := inverse && D.logN - depth ≥ 4 && (D.logN - depth) % 2 == 0
    have hn : ValidLeafNormalization D.logN depth normalize := by
      intro h
      simp only [normalize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact ⟨h.1.2, h.2⟩
    have hi : normalize = true → inverse = true := by
      intro h
      simp only [normalize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact h.1.1
    have hsize : (normalizedDifSpec D a factor normalize).size = 2 ^ D.logN :=
      size_normalizedDifSpec D a factor normalize
    have hpu : (packFields (normalizedDifSpec D a factor normalize)).size < USize.size := by
      rw [size_packFields, hsize]
      exact hu
    have hdec := decodedFields_normalizedDifSpec D a factor normalize inverse hi
    change Native.unpack (Native.natural (Native.assembleChunks (4 * 2 ^ D.logN)
      (Native.sliceInputChunks (tw.map packFields) D.logN a factor.val normalize
        (Native.sliceCount D.logN depth) depth).get) D.logN factor.val (inverse && !normalize))
        (2 ^ D.logN) = _
    rw [Native.assembleChunks_capacity, Native.sliceInputChunks_assemble tw a D.logN depth _ _ _ hs
        (TwiddlesFor.invariants D tw ht).1 hu, Native.splitInputChunks_eq,
      Native.splitInputTask_correct D tw a factor normalize depth ht hs hu hn,
      Native.natural_packFields _ _ factor _ hshape.1.2 h32 hsize hpu, hdec]
    have hd : (if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
        else NTT.Forward.forwardSpec D a).size = 2 ^ D.logN := by
      rw [← hdec]
      simp only [decodedFields, Array.size_ofFn]
    have hpd := hpu
    rw [size_packFields, hsize, ← hd, ← size_packFields] at hpd
    conv_lhs => rw [← hd]
    exact Native.unpack_packFields _ hpd
  · exact Native.run_dft D tw depth factor a inverse ht hs h32 hu

end CompPoly.CPolynomial.NTTFast.Packed
