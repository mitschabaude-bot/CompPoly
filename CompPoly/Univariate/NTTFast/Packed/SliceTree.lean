/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Native

/-! # Sliced parallel split tree for the packed FFT

Every split level runs as `P` independent chunk tasks. A chunk reads a pair of input slices
once and appends both the sum (left child) and the twiddle-scaled difference (right child)
of its index range. The children keep the chunk outputs as slices, so no level concatenates
its input; with `P = 2 ^ (depth - 1)` every leaf receives exactly one slice.
-/

@[expose] public section
open CompPoly
namespace CompPoly.CPolynomial.NTTFast.Packed.Native

/-- Sixteen sums of two word ranges. -/
@[noinline] def pairLeft (A B : @& ByteArray) (ia ib : USize) (out : ByteArray)
    (h : 4 * (ia.toNat + 15) + 3 < A.size ∧ 4 * (ib.toNat + 15) + 3 < B.size ∧
      A.size < USize.size ∧ B.size < USize.size) : ByteArray :=
  let x0 := readUOffset A ia 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x1 := readUOffset A ia 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x2 := readUOffset A ia 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x3 := readUOffset A ia 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x4 := readUOffset A ia 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x5 := readUOffset A ia 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x6 := readUOffset A ia 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x7 := readUOffset A ia 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x8 := readUOffset A ia 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x9 := readUOffset A ia 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x10 := readUOffset A ia 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x11 := readUOffset A ia 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x12 := readUOffset A ia 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x13 := readUOffset A ia 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x14 := readUOffset A ia 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x15 := readUOffset A ia 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let y0 := readUOffset B ib 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let y1 := readUOffset B ib 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let y2 := readUOffset B ib 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let y3 := readUOffset B ib 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let y4 := readUOffset B ib 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let y5 := readUOffset B ib 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let y6 := readUOffset B ib 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let y7 := readUOffset B ib 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let y8 := readUOffset B ib 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let y9 := readUOffset B ib 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let y10 := readUOffset B ib 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let y11 := readUOffset B ib 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let y12 := readUOffset B ib 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let y13 := readUOffset B ib 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let y14 := readUOffset B ib 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let y15 := readUOffset B ib 15 (by rw [usize_numeral 15 (by decide)]; omega)
  push16 out (add x0 y0) (add x1 y1) (add x2 y2) (add x3 y3) (add x4 y4) (add x5 y5) (add x6 y6)
    (add x7 y7) (add x8 y8) (add x9 y9) (add x10 y10) (add x11 y11) (add x12 y12) (add x13 y13)
    (add x14 y14) (add x15 y15)

/-- Sixteen twiddle-scaled differences of two word ranges. -/
@[noinline] def pairRight (A B w : @& ByteArray) (ia ib iw : USize) (out : ByteArray)
    (h : 4 * (ia.toNat + 15) + 3 < A.size ∧ 4 * (ib.toNat + 15) + 3 < B.size ∧
      4 * (iw.toNat + 15) + 3 < w.size ∧ A.size < USize.size ∧ B.size < USize.size ∧
      w.size < USize.size) : ByteArray :=
  let x0 := readUOffset A ia 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x1 := readUOffset A ia 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x2 := readUOffset A ia 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x3 := readUOffset A ia 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x4 := readUOffset A ia 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x5 := readUOffset A ia 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x6 := readUOffset A ia 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x7 := readUOffset A ia 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x8 := readUOffset A ia 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x9 := readUOffset A ia 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x10 := readUOffset A ia 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x11 := readUOffset A ia 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x12 := readUOffset A ia 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x13 := readUOffset A ia 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x14 := readUOffset A ia 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x15 := readUOffset A ia 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let y0 := readUOffset B ib 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let y1 := readUOffset B ib 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let y2 := readUOffset B ib 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let y3 := readUOffset B ib 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let y4 := readUOffset B ib 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let y5 := readUOffset B ib 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let y6 := readUOffset B ib 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let y7 := readUOffset B ib 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let y8 := readUOffset B ib 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let y9 := readUOffset B ib 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let y10 := readUOffset B ib 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let y11 := readUOffset B ib 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let y12 := readUOffset B ib 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let y13 := readUOffset B ib 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let y14 := readUOffset B ib 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let y15 := readUOffset B ib 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let t0 := readUOffset w iw 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let t1 := readUOffset w iw 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let t2 := readUOffset w iw 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let t3 := readUOffset w iw 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let t4 := readUOffset w iw 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let t5 := readUOffset w iw 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let t6 := readUOffset w iw 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let t7 := readUOffset w iw 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let t8 := readUOffset w iw 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let t9 := readUOffset w iw 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let t10 := readUOffset w iw 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let t11 := readUOffset w iw 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let t12 := readUOffset w iw 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let t13 := readUOffset w iw 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let t14 := readUOffset w iw 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let t15 := readUOffset w iw 15 (by rw [usize_numeral 15 (by decide)]; omega)
  push16 out (mul t0 (sub x0 y0)) (mul t1 (sub x1 y1)) (mul t2 (sub x2 y2)) (mul t3 (sub x3 y3))
    (mul t4 (sub x4 y4)) (mul t5 (sub x5 y5)) (mul t6 (sub x6 y6)) (mul t7 (sub x7 y7))
    (mul t8 (sub x8 y8)) (mul t9 (sub x9 y9)) (mul t10 (sub x10 y10)) (mul t11 (sub x11 y11))
    (mul t12 (sub x12 y12)) (mul t13 (sub x13 y13)) (mul t14 (sub x14 y14)) (mul t15 (sub x15 y15))

/-- Sixteen sums of two ranges of a field array. -/
@[noinline] def pairInputLeft (a : @& Array KoalaBear.Fast.Field) (ia ib : USize)
    (out : ByteArray) (h : ia.toNat + 15 < a.size ∧ ib.toNat + 15 < a.size ∧
      a.size < USize.size) : ByteArray :=
  let x0 := fieldAtOffset a ia 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x1 := fieldAtOffset a ia 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x2 := fieldAtOffset a ia 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x3 := fieldAtOffset a ia 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x4 := fieldAtOffset a ia 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x5 := fieldAtOffset a ia 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x6 := fieldAtOffset a ia 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x7 := fieldAtOffset a ia 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x8 := fieldAtOffset a ia 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x9 := fieldAtOffset a ia 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x10 := fieldAtOffset a ia 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x11 := fieldAtOffset a ia 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x12 := fieldAtOffset a ia 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x13 := fieldAtOffset a ia 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x14 := fieldAtOffset a ia 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x15 := fieldAtOffset a ia 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let y0 := fieldAtOffset a ib 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let y1 := fieldAtOffset a ib 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let y2 := fieldAtOffset a ib 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let y3 := fieldAtOffset a ib 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let y4 := fieldAtOffset a ib 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let y5 := fieldAtOffset a ib 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let y6 := fieldAtOffset a ib 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let y7 := fieldAtOffset a ib 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let y8 := fieldAtOffset a ib 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let y9 := fieldAtOffset a ib 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let y10 := fieldAtOffset a ib 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let y11 := fieldAtOffset a ib 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let y12 := fieldAtOffset a ib 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let y13 := fieldAtOffset a ib 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let y14 := fieldAtOffset a ib 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let y15 := fieldAtOffset a ib 15 (by rw [usize_numeral 15 (by decide)]; omega)
  push16 out (add x0 y0) (add x1 y1) (add x2 y2) (add x3 y3) (add x4 y4) (add x5 y5) (add x6 y6)
    (add x7 y7) (add x8 y8) (add x9 y9) (add x10 y10) (add x11 y11) (add x12 y12) (add x13 y13)
    (add x14 y14) (add x15 y15)

/-- Sixteen twiddle-scaled differences of two ranges of a field array. -/
@[noinline] def pairInputRight (a : @& Array KoalaBear.Fast.Field) (w : @& ByteArray)
    (ia ib iw : USize) (out : ByteArray)
    (h : ia.toNat + 15 < a.size ∧ ib.toNat + 15 < a.size ∧ 4 * (iw.toNat + 15) + 3 < w.size ∧
      a.size < USize.size ∧ w.size < USize.size) : ByteArray :=
  let x0 := fieldAtOffset a ia 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x1 := fieldAtOffset a ia 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x2 := fieldAtOffset a ia 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x3 := fieldAtOffset a ia 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x4 := fieldAtOffset a ia 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x5 := fieldAtOffset a ia 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x6 := fieldAtOffset a ia 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x7 := fieldAtOffset a ia 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x8 := fieldAtOffset a ia 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x9 := fieldAtOffset a ia 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x10 := fieldAtOffset a ia 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x11 := fieldAtOffset a ia 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x12 := fieldAtOffset a ia 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x13 := fieldAtOffset a ia 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x14 := fieldAtOffset a ia 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x15 := fieldAtOffset a ia 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let y0 := fieldAtOffset a ib 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let y1 := fieldAtOffset a ib 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let y2 := fieldAtOffset a ib 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let y3 := fieldAtOffset a ib 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let y4 := fieldAtOffset a ib 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let y5 := fieldAtOffset a ib 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let y6 := fieldAtOffset a ib 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let y7 := fieldAtOffset a ib 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let y8 := fieldAtOffset a ib 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let y9 := fieldAtOffset a ib 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let y10 := fieldAtOffset a ib 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let y11 := fieldAtOffset a ib 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let y12 := fieldAtOffset a ib 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let y13 := fieldAtOffset a ib 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let y14 := fieldAtOffset a ib 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let y15 := fieldAtOffset a ib 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let t0 := readUOffset w iw 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let t1 := readUOffset w iw 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let t2 := readUOffset w iw 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let t3 := readUOffset w iw 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let t4 := readUOffset w iw 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let t5 := readUOffset w iw 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let t6 := readUOffset w iw 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let t7 := readUOffset w iw 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let t8 := readUOffset w iw 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let t9 := readUOffset w iw 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let t10 := readUOffset w iw 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let t11 := readUOffset w iw 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let t12 := readUOffset w iw 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let t13 := readUOffset w iw 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let t14 := readUOffset w iw 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let t15 := readUOffset w iw 15 (by rw [usize_numeral 15 (by decide)]; omega)
  push16 out (mul t0 (sub x0 y0)) (mul t1 (sub x1 y1)) (mul t2 (sub x2 y2)) (mul t3 (sub x3 y3))
    (mul t4 (sub x4 y4)) (mul t5 (sub x5 y5)) (mul t6 (sub x6 y6)) (mul t7 (sub x7 y7))
    (mul t8 (sub x8 y8)) (mul t9 (sub x9 y9)) (mul t10 (sub x10 y10)) (mul t11 (sub x11 y11))
    (mul t12 (sub x12 y12)) (mul t13 (sub x13 y13)) (mul t14 (sub x14 y14)) (mul t15 (sub x15 y15))

/-- Advancing a machine index by one batch inside a buffer cannot wrap. -/
theorem usize_add16 (i : USize) (n : Nat) (h : i.toNat + 16 ≤ n) (hn : n < USize.size) :
    (i + 16).toNat = i.toNat + 16 := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  simp only [USize.toNat_add, USize.reduceToNat, hsize]
  exact Nat.mod_eq_of_lt (by omega)

/-- `n` batches of left and right split outputs at machine indices whose ranges were checked
once. -/
def pairLoop (A B w : @& ByteArray) : (n : Nat) → (ia ib iw : USize) → ByteArray → ByteArray →
    4 * (ia.toNat + 16 * n) ≤ A.size ∧ 4 * (ib.toNat + 16 * n) ≤ B.size ∧
      4 * (iw.toNat + 16 * n) ≤ w.size ∧ A.size < USize.size ∧ B.size < USize.size ∧
      w.size < USize.size → ByteArray × ByteArray
  | 0, _, _, _, l, r, _ => (l, r)
  | n + 1, ia, ib, iw, l, r, h =>
    let l := pairLeft A B ia ib l (by omega)
    let r := pairRight A B w ia ib iw r (by omega)
    pairLoop A B w n (ia + 16) (ib + 16) (iw + 16) l r (by
      rw [usize_add16 ia A.size (by omega) h.2.2.2.1, usize_add16 ib B.size (by omega) h.2.2.2.2.1,
        usize_add16 iw w.size (by omega) h.2.2.2.2.2]
      omega)

/-- Append `count` batches of left and right split outputs, from word ranges `ia` of `A` and
`ib` of `B` with twiddles from `iw`, reading each input word once; the ranges are checked once,
and out-of-range requests append nothing. -/
def pairGo (A B w : @& ByteArray) (count ia ib iw : Nat) (l r : ByteArray) :
    ByteArray × ByteArray :=
  if h : 4 * (ia + 16 * count) ≤ A.size ∧ 4 * (ib + 16 * count) ≤ B.size ∧
      4 * (iw + 16 * count) ≤ w.size ∧ A.size < USize.size ∧ B.size < USize.size ∧
      w.size < USize.size then
    pairLoop A B w count (USize.ofNatLT ia (by omega)) (USize.ofNatLT ib (by omega))
      (USize.ofNatLT iw (by omega)) l r (by simp only [USize.toNat_ofNatLT]; exact h)
  else (l, r)

/-- `pairLoop` reading both ranges from a field array. -/
def pairInputLoop (a : @& Array KoalaBear.Fast.Field) (w : @& ByteArray) :
    (n : Nat) → (ia ib iw : USize) → ByteArray → ByteArray →
    ia.toNat + 16 * n ≤ a.size ∧ ib.toNat + 16 * n ≤ a.size ∧
      4 * (iw.toNat + 16 * n) ≤ w.size ∧ a.size < USize.size ∧ w.size < USize.size →
      ByteArray × ByteArray
  | 0, _, _, _, l, r, _ => (l, r)
  | n + 1, ia, ib, iw, l, r, h =>
    let l := pairInputLeft a ia ib l (by omega)
    let r := pairInputRight a w ia ib iw r (by omega)
    pairInputLoop a w n (ia + 16) (ib + 16) (iw + 16) l r (by
      rw [usize_add16 ia a.size (by omega) h.2.2.2.1, usize_add16 ib a.size (by omega) h.2.2.2.1,
        usize_add16 iw w.size (by omega) h.2.2.2.2]
      omega)

/-- `pairGo` reading both ranges from a field array. -/
def pairInputGo (a : @& Array KoalaBear.Fast.Field) (w : @& ByteArray) (count ia ib iw : Nat)
    (l r : ByteArray) : ByteArray × ByteArray :=
  if h : ia + 16 * count ≤ a.size ∧ ib + 16 * count ≤ a.size ∧
      4 * (iw + 16 * count) ≤ w.size ∧ a.size < USize.size ∧ w.size < USize.size then
    pairInputLoop a w count (USize.ofNatLT ia (by omega)) (USize.ofNatLT ib (by omega))
      (USize.ofNatLT iw (by omega)) l r (by simp only [USize.toNat_ofNatLT]; exact h)
  else (l, r)

/-- Wait for every task without blocking a worker; results keep the task order. -/
def joinTasks (ts : Array (Task α)) : Task (Array α) :=
  ts.foldl (fun acc t ↦ acc.bind (sync := true) fun xs ↦ t.map (sync := true) fun x ↦ xs.push x)
    (.pure #[])

/-- Post-process leaves in parallel tasks. -/
def postLeaves (post : ByteArray → ByteArray) (leaves : Array ByteArray) :
    Task (Array ByteArray) :=
  joinTasks (leaves.map fun b ↦ Task.spawn fun _ ↦ post b)

/-- Whether a node of `2 ^ logN` words held as `k` slices splits into chunk tasks: a single
buffer splits into `P` chunks of whole batches, an even number of slices into slice pairs. -/
def sliceShape (logN k P : Nat) : Bool :=
  logN != 0 &&
    if k == 1 then P != 0 && 2 ^ (logN - 1) % (16 * P) == 0
    else k % 2 == 0 && 2 ^ logN % k == 0 && 2 ^ logN / k % 16 == 0

/-- The chunk tasks of one split level. -/
def sliceSplit (w : ByteArray) (logN : Nat) (slices : Array ByteArray) (P : Nat) :
    Array (Task (ByteArray × ByteArray)) :=
  let half := 2 ^ (logN - 1)
  if slices.size == 1 then
    let a := slices.getD 0 .empty
    let cs := half / P
    (Array.range P).map fun q ↦ Task.spawn fun _ ↦
      pairGo a a w (cs / 16) (q * cs) (half + q * cs) (q * cs)
        (.emptyWithCapacity (4 * cs)) (.emptyWithCapacity (4 * cs + 1))
  else
    let k := slices.size
    let s := 2 ^ logN / k
    (Array.range (k / 2)).map fun q ↦ Task.spawn fun _ ↦
      pairGo (slices.getD q .empty) (slices.getD (q + k / 2) .empty) w (s / 16) 0 0 (q * s)
        (.emptyWithCapacity (4 * s)) (.emptyWithCapacity (4 * s + 1))

/-- The buffer of a node held as slices; a single slice needs no copy. -/
def joinSlices (capacity : Nat) (slices : Array ByteArray) : ByteArray :=
  if slices.size == 1 then slices.getD 0 .empty else assembleChunks capacity slices

/-- The task tree over a node held as slices; returns the leaves in order. A leaf of
`2 ^ logN` words is computed by `leaf logN`, which stands for `post ∘ stages` and may fuse the
two; where the slices do not split, the binary tree's leaves are post-processed by `post`. -/
def sliceChunks (tw : Array ByteArray) (logN : Nat) (slices : Array ByteArray) (nInv : UInt32)
    (normalize : Bool) (P : Nat) (post : ByteArray → ByteArray)
    (leaf : Nat → ByteArray → ByteArray) : Nat → Task (Array ByteArray)
  | 0 => Task.spawn fun _ ↦ #[leaf logN (assembleChunks (4 * 2 ^ logN) slices)]
  | depth + 1 =>
    if sliceShape logN slices.size P then
      let chunks := sliceSplit (tw.getD (logN - 1) .empty) logN slices P
      (joinTasks chunks).bind (sync := true) fun rs ↦
        let left := sliceChunks tw (logN - 1) (rs.map (·.1)) nInv normalize P post leaf depth
        let right := sliceChunks tw (logN - 1) (rs.map (·.2)) nInv normalize P post leaf depth
        left.bind (sync := true) fun lo ↦ right.map (sync := true) fun hi ↦ lo ++ hi
    else (splitChunks tw logN (joinSlices (4 * 2 ^ logN) slices) nInv normalize
      (depth + 1)).bind (sync := true) (postLeaves post)

/-- The sliced task tree of a field array: the first level reads the field array directly. -/
def sliceInputChunks (tw : Array ByteArray) (logN : Nat) (a : Array KoalaBear.Fast.Field)
    (nInv : UInt32) (normalize : Bool) (P : Nat) (post : ByteArray → ByteArray)
    (leaf : Nat → ByteArray → ByteArray) (depth : Nat) :
    Task (Array ByteArray) :=
  let half := 2 ^ (logN - 1)
  if depth ≠ 0 ∧ 6 ≤ logN ∧ P ≠ 0 ∧ half % (16 * P) = 0 then
    let w := tw.getD (logN - 1) .empty
    let cs := half / P
    let chunks := (Array.range P).map fun q ↦ Task.spawn fun _ ↦
      pairInputGo a w (cs / 16) (q * cs) (half + q * cs) (q * cs)
        (.emptyWithCapacity (4 * cs)) (.emptyWithCapacity (4 * cs + 1))
    (joinTasks chunks).bind (sync := true) fun rs ↦
      let left := sliceChunks tw (logN - 1) (rs.map (·.1)) nInv normalize P post leaf
        (depth - 1)
      let right := sliceChunks tw (logN - 1) (rs.map (·.2)) nInv normalize P post leaf
        (depth - 1)
      left.bind (sync := true) fun lo ↦ right.map (sync := true) fun hi ↦ lo ++ hi
  else (splitInputChunks tw logN a nInv normalize depth).bind (sync := true) (postLeaves post)

end CompPoly.CPolynomial.NTTFast.Packed.Native
