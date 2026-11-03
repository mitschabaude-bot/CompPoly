/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.CosetLde
import CompPoly.Univariate.NTTFast.Packed.Unrolled

/-! # Coset low-degree extension of strips of eight columns

A strip holds eight columns of `h = 2 ^ m` rows interleaved word by word: word `8 r + l` is row `r`
of column `l`. A row of the strip is one vector, so every DIF butterfly between two rows is the
same butterfly in all eight columns, with its twiddle broadcast over the lanes, and no layer of
the transform shuffles within a vector. The row-major input is a strip's own layout: copying eight
words of each row gathers it, without a transpose.

A strip's coefficients are the DIF transform with the inverse twiddles, `stripLayers`, scaled by
`h` and in bit-reversed row order. Block `t` of its extension multiplies them, in natural order, by
coset table `bitrev t` and runs the forward DIF transform: the first layers read the coefficients
in bit-reversed order and multiply them as they go (`stripScaled`), out of place, and the
remaining layers run in place. The rows of the block come out in DIF order, which is the
commitment's, and eight-row transposes split them into the eight columns of the block.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Native
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

/-! ### Bounds -/

/-- A row that fits a buffer leaves room for its touched last word. -/
theorem stripRow_touch {b : ByteArray} {i : USize} (hr : 4 * (i.toNat + 8) ≤ b.size)
    (hb : b.size < USize.size) : 4 ≤ b.usize := by
  have hu : b.usize.toNat = b.size := by
    rw [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' hb]
  rw [USize.le_iff_toNat_le, hu, usize_numeral 4 (by decide)]
  omega

/-- Word `k < 8` of a row that fits `b` fits every buffer of `b`'s size. -/
theorem stripRow_read {b o : ByteArray} {i : USize} (hr : 4 * (i.toNat + 8) ≤ b.size)
    (hb : b.size < USize.size) (ho : o.size = b.size) (k : Nat) (hk : k < 8) :
    4 * (i.toNat + (OfNat.ofNat k : USize).toNat) + 3 < o.size ∧ o.size < USize.size := by
  rw [usize_numeral k (by omega), ho]
  exact ⟨by omega, hb⟩

/-- A word that fits a table can be read. -/
theorem stripWord_read {t : ByteArray} {j : USize} (hj : 4 * (j.toNat + 1) ≤ t.size)
    (ht : t.size < USize.size) :
    4 * (j.toNat + (0 : USize).toNat) + 3 < t.size ∧ t.size < USize.size := by
  rw [USize.toNat_zero]
  exact ⟨by omega, ht⟩

/-- A row that fits `b` can be stored. -/
theorem stripRow_store {b : ByteArray} {i : USize} (hr : 4 * (i.toNat + 8) ≤ b.size)
    (hb : b.size < USize.size) :
    (i * 4).toNat + 4 * 8 ≤ b.size ∧ (i * 4).toNat + 4 * 8 < USize.size := by
  rw [wordOffset_toNat' i (by omega)]
  omega

/-! ### Row kernels -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- One radix-four DIF row in place: rows `i0, …, i3` of `b`, twiddles `th[j]`, `th[j1]`, `tl[j]`
for all eight lanes. -/
@[inline] def stripQuad (p : ℕ) [Mont32Field p] (th tl : @& ByteArray) (j j1 i0 i1 i2 i3 : USize)
    (b : ByteArray) (hr0 : 4 * (i0.toNat + 8) ≤ b.size) (hr1 : 4 * (i1.toNat + 8) ≤ b.size)
    (hr2 : 4 * (i2.toNat + 8) ≤ b.size) (hr3 : 4 * (i3.toNat + 8) ≤ b.size)
    (hb : b.size < USize.size) (hwj : 4 * (j.toNat + 1) ≤ th.size)
    (hwj1 : 4 * (j1.toNat + 1) ≤ th.size) (hth : th.size < USize.size)
    (hwl : 4 * (j.toNat + 1) ≤ tl.size) (htl : tl.size < USize.size) : Buf b.size :=
  stripQuad_words%

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The last radix-four DIF pass on one block in place: rows `i0, …, i3` of `b`, twiddles `1`,
`w1` and `1` for all eight lanes. -/
@[inline] def stripLast (p : ℕ) [Mont32Field p] (w1 : UInt32) (i0 i1 i2 i3 : USize)
    (b : ByteArray) (hr0 : 4 * (i0.toNat + 8) ≤ b.size) (hr1 : 4 * (i1.toNat + 8) ≤ b.size)
    (hr2 : 4 * (i2.toNat + 8) ≤ b.size) (hr3 : 4 * (i3.toNat + 8) ≤ b.size)
    (hb : b.size < USize.size) : Buf b.size :=
  stripLast_words%

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- One radix-two DIF row in place: rows `i0`, `i1` of `b`, twiddle `tw[j]` for all eight
lanes. -/
@[inline] def stripPair (p : ℕ) [Mont32Field p] (tw : @& ByteArray) (j i0 i1 : USize)
    (b : ByteArray) (hr0 : 4 * (i0.toNat + 8) ≤ b.size) (hr1 : 4 * (i1.toNat + 8) ≤ b.size)
    (hb : b.size < USize.size) (hwj : 4 * (j.toNat + 1) ≤ tw.size) (htw : tw.size < USize.size) :
    Buf b.size :=
  stripPair_words%

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The first radix-four DIF row of a coset block, out of place: rows `s0, …, s3` of `src` times
words `t0, …, t3` of `T`, through the butterflies with twiddles `th[j]`, `th[j1]`, `tl[j]`, into
rows `i0, …, i3` of `out`. -/
@[inline] def stripScaledQuad (p : ℕ) [Mont32Field p] (th tl T src : @& ByteArray)
    (j j1 t0 t1 t2 t3 s0 s1 s2 s3 i0 i1 i2 i3 : USize) (out : ByteArray)
    (hr0 : 4 * (i0.toNat + 8) ≤ out.size) (hr1 : 4 * (i1.toNat + 8) ≤ out.size)
    (hr2 : 4 * (i2.toNat + 8) ≤ out.size) (hr3 : 4 * (i3.toNat + 8) ≤ out.size)
    (hb : out.size < USize.size)
    (hs0 : 4 * (s0.toNat + 8) ≤ src.size) (hs1 : 4 * (s1.toNat + 8) ≤ src.size)
    (hs2 : 4 * (s2.toNat + 8) ≤ src.size) (hs3 : 4 * (s3.toNat + 8) ≤ src.size)
    (hsrc : src.size < USize.size)
    (ht0 : 4 * (t0.toNat + 1) ≤ T.size) (ht1 : 4 * (t1.toNat + 1) ≤ T.size)
    (ht2 : 4 * (t2.toNat + 1) ≤ T.size) (ht3 : 4 * (t3.toNat + 1) ≤ T.size)
    (hT : T.size < USize.size) (hwj : 4 * (j.toNat + 1) ≤ th.size)
    (hwj1 : 4 * (j1.toNat + 1) ≤ th.size) (hth : th.size < USize.size)
    (hwl : 4 * (j.toNat + 1) ≤ tl.size) (htl : tl.size < USize.size) : Buf out.size :=
  stripScaledQuad_words%

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The first radix-two DIF row of a coset block, out of place: rows `s0`, `s1` of `src` times
words `t0`, `t1` of `T`, through the butterfly with twiddle `tw[j]`, into rows `i0`, `i1` of
`out`. -/
@[inline] def stripScaledPair (p : ℕ) [Mont32Field p] (tw T src : @& ByteArray)
    (j t0 t1 s0 s1 i0 i1 : USize) (out : ByteArray)
    (hr0 : 4 * (i0.toNat + 8) ≤ out.size) (hr1 : 4 * (i1.toNat + 8) ≤ out.size)
    (hb : out.size < USize.size)
    (hs0 : 4 * (s0.toNat + 8) ≤ src.size) (hs1 : 4 * (s1.toNat + 8) ≤ src.size)
    (hsrc : src.size < USize.size)
    (ht0 : 4 * (t0.toNat + 1) ≤ T.size) (ht1 : 4 * (t1.toNat + 1) ≤ T.size)
    (hT : T.size < USize.size) (hwj : 4 * (j.toNat + 1) ≤ tw.size)
    (htw : tw.size < USize.size) : Buf out.size :=
  stripScaledPair_words%

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Rows `s0, …, s7` of eight words of `src` copied to rows `i0, …, i7` of `out`. -/
@[noinline] def stripRows8 (src : @& ByteArray) (s0 s1 s2 s3 s4 s5 s6 s7 : USize)
    (i0 i1 i2 i3 i4 i5 i6 i7 : USize) (out : ByteArray)
    (hr0 : 4 * (i0.toNat + 8) ≤ out.size) (hr1 : 4 * (i1.toNat + 8) ≤ out.size)
    (hr2 : 4 * (i2.toNat + 8) ≤ out.size) (hr3 : 4 * (i3.toNat + 8) ≤ out.size)
    (hr4 : 4 * (i4.toNat + 8) ≤ out.size) (hr5 : 4 * (i5.toNat + 8) ≤ out.size)
    (hr6 : 4 * (i6.toNat + 8) ≤ out.size) (hr7 : 4 * (i7.toNat + 8) ≤ out.size)
    (hb : out.size < USize.size)
    (hs0 : 4 * (s0.toNat + 8) ≤ src.size) (hs1 : 4 * (s1.toNat + 8) ≤ src.size)
    (hs2 : 4 * (s2.toNat + 8) ≤ src.size) (hs3 : 4 * (s3.toNat + 8) ≤ src.size)
    (hs4 : 4 * (s4.toNat + 8) ≤ src.size) (hs5 : 4 * (s5.toNat + 8) ≤ src.size)
    (hs6 : 4 * (s6.toNat + 8) ≤ src.size) (hs7 : 4 * (s7.toNat + 8) ≤ src.size)
    (hsrc : src.size < USize.size) : Buf out.size :=
  stripRows8_words%

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The transpose of rows `s0, …, s7` of `src`: lane `u` of them stored as row `i{u}` of `out`. -/
@[noinline] def stripTranspose8 (src : @& ByteArray) (s0 s1 s2 s3 s4 s5 s6 s7 : USize)
    (i0 i1 i2 i3 i4 i5 i6 i7 : USize) (out : ByteArray)
    (hr0 : 4 * (i0.toNat + 8) ≤ out.size) (hr1 : 4 * (i1.toNat + 8) ≤ out.size)
    (hr2 : 4 * (i2.toNat + 8) ≤ out.size) (hr3 : 4 * (i3.toNat + 8) ≤ out.size)
    (hr4 : 4 * (i4.toNat + 8) ≤ out.size) (hr5 : 4 * (i5.toNat + 8) ≤ out.size)
    (hr6 : 4 * (i6.toNat + 8) ≤ out.size) (hr7 : 4 * (i7.toNat + 8) ≤ out.size)
    (hb : out.size < USize.size)
    (hs0 : 4 * (s0.toNat + 8) ≤ src.size) (hs1 : 4 * (s1.toNat + 8) ≤ src.size)
    (hs2 : 4 * (s2.toNat + 8) ≤ src.size) (hs3 : 4 * (s3.toNat + 8) ≤ src.size)
    (hs4 : 4 * (s4.toNat + 8) ≤ src.size) (hs5 : 4 * (s5.toNat + 8) ≤ src.size)
    (hs6 : 4 * (s6.toNat + 8) ≤ src.size) (hs7 : 4 * (s7.toNat + 8) ≤ src.size)
    (hsrc : src.size < USize.size) : Buf out.size :=
  stripTranspose8_words%

/-! ### Passes -/

/-- A buffer's value has its size. -/
theorem size_buf {n : Nat} (x : Buf n) : x.1.size = n := x.2

/-- `k · y` for a numeral `k < 8` does not wrap below the word size. -/
theorem usize_mul_small (k : Nat) (y : USize) (hk : k < 8) (h : k * y.toNat < USize.size) :
    (OfNat.ofNat k * y : USize).toNat = k * y.toNat :=
  usize_mul_toNat k y (by omega) h

/-- `n` radix-four rows from row `i0` with quarters `qq` words apart, twiddles from `j` and `j1`,
after one range check. -/
@[specialize]
def stripQuadRows (p : ℕ) [Mont32Field p] (th tl : @& ByteArray) (qq : USize) :
    (n : Nat) → (j j1 i0 : USize) → (b : ByteArray) →
    4 * (i0.toNat + 3 * qq.toNat + 8 * n) ≤ b.size ∧ b.size < USize.size ∧
      4 * (j.toNat + n) ≤ th.size ∧ 4 * (j1.toNat + n) ≤ th.size ∧ th.size < USize.size ∧
      4 * (j.toNat + n) ≤ tl.size ∧ tl.size < USize.size → ByteArray
  | 0, _, _, _, b, _ => b
  | n + 1, j, j1, i0, b, h =>
    have h1 : (i0 + qq).toNat = i0.toNat + qq.toNat := usize_add_toNat _ _ (by omega)
    have h2 : (i0 + 2 * qq).toNat = i0.toNat + 2 * qq.toNat := by
      rw [usize_add_toNat _ _ (by rw [usize_mul_small 2 qq (by decide) (by omega)]; omega),
        usize_mul_small 2 qq (by decide) (by omega)]
    have h3 : (i0 + 3 * qq).toNat = i0.toNat + 3 * qq.toNat := by
      rw [usize_add_toNat _ _ (by rw [usize_mul_small 3 qq (by decide) (by omega)]; omega),
        usize_mul_small 3 qq (by decide) (by omega)]
    have hi8 : (i0 + 8).toNat = i0.toNat + 8 := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral 8 (by decide)]; omega),
        usize_numeral 8 (by decide)]
    have hj : (j + 1).toNat = j.toNat + 1 := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral 1 (by decide)]; omega),
        usize_numeral 1 (by decide)]
    have hj1 : (j1 + 1).toNat = j1.toNat + 1 := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral 1 (by decide)]; omega),
        usize_numeral 1 (by decide)]
    let b' := stripQuad p th tl j j1 i0 (i0 + qq) (i0 + 2 * qq) (i0 + 3 * qq) b (by omega)
      (by rw [h1]; omega) (by rw [h2]; omega) (by rw [h3]; omega) h.2.1 (by omega) (by omega)
      h.2.2.2.2.1 (by omega) h.2.2.2.2.2.2
    stripQuadRows p th tl qq n (j + 1) (j1 + 1) (i0 + 8) b'.1 (by
      rw [b'.2, hi8, hj, hj1]
      omega)

/-- The row loop keeps the buffer size. -/
theorem size_stripQuadRows (th tl : ByteArray) (qq : USize) : ∀ (n : Nat) (j j1 i0 : USize)
    (b : ByteArray) (h), (stripQuadRows p th tl qq n j j1 i0 b h).size = b.size
  | 0, _, _, _, _, _ => rfl
  | n + 1, j, j1, i0, b, h => by
    rw [stripQuadRows, size_stripQuadRows th tl qq n]
    exact size_buf _

/-- `blocks` radix-four blocks of quarter `q` rows from word `base`, after one range check. -/
@[specialize]
def stripQuadBlocks (p : ℕ) [Mont32Field p] (th tl : @& ByteArray) (q : USize) :
    (blocks : Nat) → (base : USize) → (b : ByteArray) →
    4 * (base.toNat + 32 * q.toNat * blocks) ≤ b.size ∧ b.size < USize.size ∧
      4 * (2 * q.toNat) ≤ th.size ∧ th.size < USize.size ∧ 4 * q.toNat ≤ tl.size ∧
      tl.size < USize.size → ByteArray
  | 0, _, b, _ => b
  | blocks + 1, base, b, h =>
    have hc : 32 * q.toNat ≤ 32 * q.toNat * (blocks + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h8 : (8 * q).toNat = 8 * q.toNat := usize_mul_toNat 8 q (by decide) (by omega)
    have h32 : (32 * q).toNat = 32 * q.toNat := usize_mul_toNat 32 q (by decide) (by omega)
    have hn : (base + 32 * q).toNat = base.toNat + 32 * q.toNat := by
      rw [usize_add_toNat _ _ (by rw [h32]; omega), h32]
    have hrow : 4 * (base.toNat + 3 * (8 * q).toNat + 8 * q.toNat) ≤ b.size ∧
        b.size < USize.size ∧ 4 * ((0 : USize).toNat + q.toNat) ≤ th.size ∧
        4 * (q.toNat + q.toNat) ≤ th.size ∧ th.size < USize.size ∧
        4 * ((0 : USize).toNat + q.toNat) ≤ tl.size ∧ tl.size < USize.size := by
      rw [h8, USize.toNat_zero]
      omega
    let b' := stripQuadRows p th tl (8 * q) q.toNat 0 q base b hrow
    stripQuadBlocks p th tl q blocks (base + 32 * q) b' (by
      rw [size_stripQuadRows, hn, Nat.mul_succ] at *
      omega)

/-- `blocks` blocks of the last radix-four pass, four rows each, from word `base`, with twiddles
`1`, `w1`, `1`, after one range check. -/
@[specialize]
def stripLastBlocks (p : ℕ) [Mont32Field p] (w1 : UInt32) :
    (blocks : Nat) → (base : USize) → (b : ByteArray) →
    4 * (base.toNat + 32 * blocks) ≤ b.size ∧ b.size < USize.size → ByteArray
  | 0, _, b, _ => b
  | blocks + 1, base, b, h =>
    have hc (o : Nat) (ho : o ≤ 32) : (base + OfNat.ofNat o).toNat = base.toNat + o := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral o (by omega)]; omega),
        usize_numeral o (by omega)]
    let b' := stripLast p w1 (base + 0) (base + 8) (base + 16) (base + 24) b
      (by rw [hc 0 (by decide)]; omega) (by rw [hc 8 (by decide)]; omega)
      (by rw [hc 16 (by decide)]; omega) (by rw [hc 24 (by decide)]; omega) h.2
    stripLastBlocks p w1 blocks (base + 32) b'.1 (by
      rw [b'.2, hc 32 (by decide)]
      omega)

/-- A radix-four DIF pass of quarter `q` rows over `blocks` blocks of a strip, with twiddle tables
`th` (of `2 q`) and `tl` (of `q`). The last pass, of quarter one row, takes the twiddles `1`,
`th[1]` and `1` of its tables. -/
@[noinline, specialize]
def stripRadix4 (p : ℕ) [Mont32Field p] (th tl : @& ByteArray) (q blocks : Nat) (b : ByteArray) :
    ByteArray :=
  if h : 4 * (32 * q * blocks) ≤ b.size ∧ b.size < USize.size ∧ 4 * (2 * q) ≤ th.size ∧
      th.size < USize.size ∧ 4 * q ≤ tl.size ∧ tl.size < USize.size then
    if hq : q = 1 then
      stripLastBlocks p (read th 1) blocks 0 b (by
        rw [USize.toNat_zero, Nat.zero_add]
        subst hq
        omega)
    else
      stripQuadBlocks p th tl (USize.ofNatLT q (by omega)) blocks 0 b (by
        rw [USize.toNat_ofNatLT, USize.toNat_zero, Nat.zero_add]
        exact h)
  else b

/-- `n` radix-two rows from row `i0` with halves `qq` words apart, twiddles from `j`, after one
range check. -/
@[specialize]
def stripPairRows (p : ℕ) [Mont32Field p] (tw : @& ByteArray) (qq : USize) :
    (n : Nat) → (j i0 : USize) → (b : ByteArray) →
    4 * (i0.toNat + qq.toNat + 8 * n) ≤ b.size ∧ b.size < USize.size ∧
      4 * (j.toNat + n) ≤ tw.size ∧ tw.size < USize.size → ByteArray
  | 0, _, _, b, _ => b
  | n + 1, j, i0, b, h =>
    have h1 : (i0 + qq).toNat = i0.toNat + qq.toNat := usize_add_toNat _ _ (by omega)
    have hi8 : (i0 + 8).toNat = i0.toNat + 8 := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral 8 (by decide)]; omega),
        usize_numeral 8 (by decide)]
    have hj : (j + 1).toNat = j.toNat + 1 := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral 1 (by decide)]; omega),
        usize_numeral 1 (by decide)]
    let b' := stripPair p tw j i0 (i0 + qq) b (by omega) (by rw [h1]; omega) h.2.1 (by omega)
      h.2.2.2
    stripPairRows p tw qq n (j + 1) (i0 + 8) b'.1 (by
      rw [b'.2, hi8, hj]
      omega)

/-- The radix-two DIF layer of half `half` rows of a strip, with twiddle table `tw` (of
`half`). -/
@[noinline, specialize]
def stripRadix2 (p : ℕ) [Mont32Field p] (tw : @& ByteArray) (half : Nat) (b : ByteArray) :
    ByteArray :=
  if h : 4 * (16 * half) ≤ b.size ∧ b.size < USize.size ∧ 4 * half ≤ tw.size ∧
      tw.size < USize.size then
    stripPairRows p tw (USize.ofNatLT (8 * half) (by omega)) half 0 0 b (by
      rw [USize.toNat_ofNatLT, USize.toNat_zero]
      omega)
  else b

/-- The radix-four DIF passes `start, …` of a `2 ^ m`-row strip, those of `fieldLayers`. -/
@[specialize]
def stripLayersFrom (p : ℕ) [Mont32Field p] (tw : @& Array ByteArray) (m start : Nat)
    (b : ByteArray) : ByteArray :=
  (List.range' start (m / 2 - start)).foldl (fun b pass ↦
    let high := m - 1 - m % 2 - 2 * pass
    let q := 2 ^ (high - 1)
    stripRadix4 p (tw.getD high .empty) (tw.getD (high - 1) .empty) q (2 ^ m / (4 * q)) b) b

/-- The DIF transform of a `2 ^ m`-row strip with twiddle tables `tw`, in place: a radix-two layer
first if `m` is odd, then radix-four passes. -/
@[specialize]
def stripLayers (p : ℕ) [Mont32Field p] (tw : @& Array ByteArray) (m : Nat) (b : ByteArray) :
    ByteArray :=
  stripLayersFrom p tw m 0
    (if m % 2 = 1 then stripRadix2 p (tw.getD (m - 1) .empty) (2 ^ (m - 1)) b else b)

/-! ### Coset blocks -/

/-- The ranges a scaled first radix-four row from row `k` needs, quarters of `q` rows. -/
abbrev ScaledQuadFits (th tl T src out : ByteArray) (q k : USize) : Prop :=
  4 * (8 * (k.toNat + 3 * q.toNat) + 8) ≤ out.size ∧ out.size < USize.size ∧
    src.size < USize.size ∧ 4 * (k.toNat + 3 * q.toNat + 1) ≤ T.size ∧ T.size < USize.size ∧
    4 * (k.toNat + q.toNat + 1) ≤ th.size ∧ th.size < USize.size ∧
    4 * (k.toNat + 1) ≤ tl.size ∧ tl.size < USize.size

/-- Row `k` of the scaled first radix-four pass of a block with quarters of `q` rows: row
`k + c q` of `out` is row `bitrev (k + c q) = R + bitrev c` of `src`, `R = bitrev k` (the shift
`sh` reverses the block's bits), times word `k + c q` of `T`, through the butterflies with
twiddles `th[k]`, `th[k + q]`, `tl[k]`. A row whose source does not fit is skipped. -/
@[inline] def stripScaledQuadCell (p : ℕ) [Mont32Field p] (th tl T src : @& ByteArray) (q : USize)
    (sh : UInt32) (k : USize) (out : ByteArray) (h : ScaledQuadFits th tl T src out q k) :
    ByteArray :=
  let R := 8 * (reverse32 k.toUInt32 >>> sh).toUSize
  if hs : 4 * (R.toNat + 32) ≤ src.size then
    have hq1 : (k + q).toNat = k.toNat + q.toNat := usize_add_toNat _ _ (by omega)
    have hq2 : (k + 2 * q).toNat = k.toNat + 2 * q.toNat := by
      rw [usize_add_toNat _ _ (by rw [usize_mul_small 2 q (by decide) (by omega)]; omega),
        usize_mul_small 2 q (by decide) (by omega)]
    have hq3 : (k + 3 * q).toNat = k.toNat + 3 * q.toNat := by
      rw [usize_add_toNat _ _ (by rw [usize_mul_small 3 q (by decide) (by omega)]; omega),
        usize_mul_small 3 q (by decide) (by omega)]
    have hrow (x : USize) (hx : 4 * (8 * x.toNat + 8) ≤ out.size) :
        4 * ((8 * x).toNat + 8) ≤ out.size := by
      rw [usize_mul_toNat 8 x (by decide) (by omega)]
      omega
    have hR (o : Nat) (ho : o ≤ 24) : (R + OfNat.ofNat o).toNat = R.toNat + o := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral o (by omega)]; omega),
        usize_numeral o (by omega)]
    (stripScaledQuad p th tl T src k (k + q) k (k + q) (k + 2 * q) (k + 3 * q) R (R + 16)
      (R + 8) (R + 24) (8 * k) (8 * (k + q)) (8 * (k + 2 * q)) (8 * (k + 3 * q)) out
      (hrow k (by omega)) (hrow _ (by rw [hq1]; omega)) (hrow _ (by rw [hq2]; omega))
      (hrow _ (by rw [hq3]; omega)) h.2.1 (by omega) (by rw [hR 16 (by decide)]; omega)
      (by rw [hR 8 (by decide)]; omega) (by rw [hR 24 (by decide)]; omega) h.2.2.1
      (by omega) (by rw [hq1]; omega) (by rw [hq2]; omega) (by rw [hq3]; omega) h.2.2.2.2.1
      (by omega) (by rw [hq1]; omega) h.2.2.2.2.2.2.1 (by omega) h.2.2.2.2.2.2.2.2).1
  else out

theorem size_stripScaledQuadCell (th tl T src : ByteArray) (q : USize) (sh : UInt32)
    (k : USize) (out : ByteArray) (h) :
    (stripScaledQuadCell p th tl T src q sh k out h).size = out.size := by
  unfold stripScaledQuadCell
  dsimp only
  split
  · exact size_buf _
  · rfl

/-- Rows `k, …, k + n - 1` of the scaled first radix-four pass (`stripScaledQuadCell`), after
one range check. -/
@[specialize]
def stripScaledQuadRows (p : ℕ) [Mont32Field p] (th tl T src : @& ByteArray) (q : USize)
    (sh : UInt32) : (n : Nat) → (k : USize) → (out : ByteArray) →
    4 * (8 * (k.toNat + 3 * q.toNat + n)) ≤ out.size ∧ out.size < USize.size ∧
      src.size < USize.size ∧ 4 * (k.toNat + 3 * q.toNat + n) ≤ T.size ∧ T.size < USize.size ∧
      4 * (k.toNat + q.toNat + n) ≤ th.size ∧ th.size < USize.size ∧
      4 * (k.toNat + n) ≤ tl.size ∧ tl.size < USize.size → ByteArray
  | 0, _, out, _ => out
  | n + 1, k, out, h =>
    have hk1 : (k + 1).toNat = k.toNat + 1 := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral 1 (by decide)]; omega),
        usize_numeral 1 (by decide)]
    stripScaledQuadRows p th tl T src q sh n (k + 1)
      (stripScaledQuadCell p th tl T src q sh k out (by omega)) (by
        rw [size_stripScaledQuadCell, hk1]
        omega)

/-- The ranges a scaled first radix-two row from row `k` needs, halves of `q` rows. -/
abbrev ScaledPairFits (tw T src out : ByteArray) (q k : USize) : Prop :=
  4 * (8 * (k.toNat + q.toNat) + 8) ≤ out.size ∧ out.size < USize.size ∧
    src.size < USize.size ∧ 4 * (k.toNat + q.toNat + 1) ≤ T.size ∧ T.size < USize.size ∧
    4 * (k.toNat + 1) ≤ tw.size ∧ tw.size < USize.size

/-- Row `k` of the scaled first radix-two layer of a block with halves of `q` rows: row `k + c q`
of `out` is row `bitrev (k + c q) = R + c` of `src`, `R = bitrev k`, times word `k + c q` of `T`,
through the butterfly with twiddle `tw[k]`. A row whose source does not fit is skipped. -/
@[inline] def stripScaledPairCell (p : ℕ) [Mont32Field p] (tw T src : @& ByteArray) (q : USize)
    (sh : UInt32) (k : USize) (out : ByteArray) (h : ScaledPairFits tw T src out q k) :
    ByteArray :=
  let R := 8 * (reverse32 k.toUInt32 >>> sh).toUSize
  if hs : 4 * (R.toNat + 16) ≤ src.size then
    have hq1 : (k + q).toNat = k.toNat + q.toNat := usize_add_toNat _ _ (by omega)
    have hrow (x : USize) (hx : 4 * (8 * x.toNat + 8) ≤ out.size) :
        4 * ((8 * x).toNat + 8) ≤ out.size := by
      rw [usize_mul_toNat 8 x (by decide) (by omega)]
      omega
    have hR : (R + 8).toNat = R.toNat + 8 := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral 8 (by decide)]; omega),
        usize_numeral 8 (by decide)]
    (stripScaledPair p tw T src k k (k + q) R (R + 8) (8 * k) (8 * (k + q)) out
      (hrow k (by omega)) (hrow _ (by rw [hq1]; omega)) h.2.1 (by omega) (by rw [hR]; omega)
      h.2.2.1 (by omega) (by rw [hq1]; omega) h.2.2.2.2.1 (by omega) h.2.2.2.2.2.2).1
  else out

theorem size_stripScaledPairCell (tw T src : ByteArray) (q : USize) (sh : UInt32)
    (k : USize) (out : ByteArray) (h) :
    (stripScaledPairCell p tw T src q sh k out h).size = out.size := by
  unfold stripScaledPairCell
  dsimp only
  split
  · exact size_buf _
  · rfl

/-- Rows `k, …, k + n - 1` of the scaled first radix-two layer (`stripScaledPairCell`), after one
range check. -/
@[specialize]
def stripScaledPairRows (p : ℕ) [Mont32Field p] (tw T src : @& ByteArray) (q : USize)
    (sh : UInt32) : (n : Nat) → (k : USize) → (out : ByteArray) →
    4 * (8 * (k.toNat + q.toNat + n)) ≤ out.size ∧ out.size < USize.size ∧
      src.size < USize.size ∧ 4 * (k.toNat + q.toNat + n) ≤ T.size ∧ T.size < USize.size ∧
      4 * (k.toNat + n) ≤ tw.size ∧ tw.size < USize.size → ByteArray
  | 0, _, out, _ => out
  | n + 1, k, out, h =>
    have hk1 : (k + 1).toNat = k.toNat + 1 := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral 1 (by decide)]; omega),
        usize_numeral 1 (by decide)]
    stripScaledPairRows p tw T src q sh n (k + 1)
      (stripScaledPairCell p tw T src q sh k out (by omega)) (by
        rw [size_stripScaledPairCell, hk1]
        omega)

/-- The coset product with `T` of the coefficients `C` of a `2 ^ m`-row strip, in bit-reversed
order, and the first layers of its DIF transform with twiddle tables `tw`, out of place: the
radix-two layer if `m` is odd, else the first radix-four pass. -/
@[noinline, specialize]
def stripScaled (p : ℕ) [Mont32Field p] (tw : @& Array ByteArray) (T C : @& ByteArray) (m : Nat) :
    ByteArray :=
  let out := zeroWords (8 * 2 ^ m)
  let sh := (32 - m).toUInt32
  if m % 2 = 1 then
    let tw1 := tw.getD (m - 1) .empty
    let q := 2 ^ (m - 1)
    if h : 4 * (8 * (2 * q)) ≤ out.size ∧ out.size < USize.size ∧ C.size < USize.size ∧
        4 * (2 * q) ≤ T.size ∧ T.size < USize.size ∧ 4 * q ≤ tw1.size ∧
        tw1.size < USize.size then
      stripScaledPairRows p tw1 T C (USize.ofNatLT q (by omega)) sh q 0 out (by
        rw [USize.toNat_ofNatLT, USize.toNat_zero]
        omega)
    else out
  else
    let th := tw.getD (m - 1) .empty
    let tl := tw.getD (m - 2) .empty
    let q := 2 ^ (m - 2)
    if h : 4 * (8 * (4 * q)) ≤ out.size ∧ out.size < USize.size ∧ C.size < USize.size ∧
        4 * (4 * q) ≤ T.size ∧ T.size < USize.size ∧ 4 * (2 * q) ≤ th.size ∧
        th.size < USize.size ∧ 4 * q ≤ tl.size ∧ tl.size < USize.size then
      stripScaledQuadRows p th tl T C (USize.ofNatLT q (by omega)) sh q 0 out (by
        rw [USize.toNat_ofNatLT, USize.toNat_zero]
        omega)
    else out

/-! ### Gathering and splitting -/

/-- Line `t < 8` of lines `qs` words apart from word `q` fits a buffer that the last line fits. -/
theorem stripLine_fits {b : ByteArray} {q qs : USize}
    (h : 4 * (q.toNat + 7 * qs.toNat + 8) ≤ b.size) (hb : b.size < USize.size) (t : Nat)
    (ht : t < 8) :
    4 * ((q + OfNat.ofNat t * qs).toNat + 8) ≤ b.size := by
  have hm : t * qs.toNat ≤ 7 * qs.toNat := Nat.mul_le_mul_right _ (by omega)
  rw [usize_add_toNat _ _ (by rw [usize_mul_small t qs ht (by omega)]; omega),
    usize_mul_small t qs ht (by omega)]
  omega

/-- Lines `q, q + qs, …, q + 7 qs` of eight words of `src` copied to rows `p, …, p + 7` of
`out`, if they fit. -/
@[inline] def stripCopy8 (src : @& ByteArray) (q qs : USize) (out : ByteArray) (p : USize) :
    ByteArray :=
  if h : 4 * (q.toNat + 7 * qs.toNat + 8) ≤ src.size ∧ src.size < USize.size ∧
      4 * (p.toNat + 7 * 8 + 8) ≤ out.size ∧ out.size < USize.size then
    have hs := stripLine_fits h.1 h.2.1
    have ho := stripLine_fits (qs := 8) (by rw [usize_numeral 8 (by decide)]; exact h.2.2.1)
      h.2.2.2
    (stripRows8 src (q + 0 * qs) (q + 1 * qs) (q + 2 * qs) (q + 3 * qs) (q + 4 * qs) (q + 5 * qs)
      (q + 6 * qs) (q + 7 * qs) (p + 0 * 8) (p + 1 * 8) (p + 2 * 8) (p + 3 * 8) (p + 4 * 8)
      (p + 5 * 8)
      (p + 6 * 8) (p + 7 * 8) out
      (ho 0 (by decide)) (ho 1 (by decide)) (ho 2 (by decide))
      (ho 3 (by decide)) (ho 4 (by decide)) (ho 5 (by decide)) (ho 6 (by decide))
      (ho 7 (by decide)) h.2.2.2
      (hs 0 (by decide)) (hs 1 (by decide)) (hs 2 (by decide))
      (hs 3 (by decide)) (hs 4 (by decide)) (hs 5 (by decide)) (hs 6 (by decide))
      (hs 7 (by decide)) h.2.1).1
  else out

/-- Strip `s`, columns `8 s, …, 8 s + 7`, of the row-major matrix of width `w` whose rows are the
chunks `ms` of `rows` rows each, `rows` a multiple of eight. -/
def stripOfChunks (ms : @& Array ByteArray) (w s rows : Nat) : ByteArray := Id.run do
  let mut out := zeroWords (8 * (ms.size * rows))
  for c in [:ms.size] do
    let m := ms.getD c .empty
    for rb in [:rows / 8] do
      out := stripCopy8 m (8 * rb * w + 8 * s).toUSize w.toUSize out
        (8 * (c * rows + 8 * rb)).toUSize
  return out

/-- The transpose of rows `q, …, q + 7` of `src` stored as lines `p, p + ps, …, p + 7 ps` of
`out`, if they fit. -/
@[inline] def stripSplit8 (src : @& ByteArray) (q : USize) (out : ByteArray) (p ps : USize) :
    ByteArray :=
  if h : 4 * (q.toNat + 7 * 8 + 8) ≤ src.size ∧ src.size < USize.size ∧
      4 * (p.toNat + 7 * ps.toNat + 8) ≤ out.size ∧ out.size < USize.size then
    have hs := stripLine_fits (qs := 8) (by rw [usize_numeral 8 (by decide)]; exact h.1) h.2.1
    have ho := stripLine_fits h.2.2.1 h.2.2.2
    (stripTranspose8 src (q + 0 * 8) (q + 1 * 8) (q + 2 * 8) (q + 3 * 8) (q + 4 * 8) (q + 5 * 8)
      (q + 6 * 8) (q + 7 * 8) (p + 0 * ps) (p + 1 * ps) (p + 2 * ps) (p + 3 * ps) (p + 4 * ps)
      (p + 5 * ps)
      (p + 6 * ps) (p + 7 * ps) out
      (ho 0 (by decide)) (ho 1 (by decide)) (ho 2 (by decide))
      (ho 3 (by decide)) (ho 4 (by decide)) (ho 5 (by decide)) (ho 6 (by decide))
      (ho 7 (by decide)) h.2.2.2
      (hs 0 (by decide)) (hs 1 (by decide)) (hs 2 (by decide))
      (hs 3 (by decide)) (hs 4 (by decide)) (hs 5 (by decide)) (hs 6 (by decide))
      (hs 7 (by decide)) h.2.1).1
  else out

/-- The eight columns of a strip of `h` rows, `h` a multiple of eight. -/
def stripColumns (Y : @& ByteArray) (h : Nat) : Array ByteArray := Id.run do
  let mut out := zeroWords (8 * h)
  for rb in [:h / 8] do
    out := stripSplit8 Y (64 * rb).toUSize out (8 * rb).toUSize h.toUSize
  return (Array.range 8).map fun l ↦
    out.copySlice (4 * (l * h)) (ByteArray.emptyWithCapacity (4 * h)) 0 (4 * h)

/-! ### Extension -/

/-- A strip's coefficients, scaled by `h` and in bit-reversed row order: its DIF transform with
the inverse twiddles. -/
@[specialize]
def stripCoefficients (P : LdePlan p) (S : ByteArray) : ByteArray :=
  stripLayers p P.inverseTwiddles P.logH S

/-- Block `t` of the extension of a strip with coefficients `C` (`stripCoefficients`), as the
eight columns of the block: the values on coset `bitrev t` in DIF order. -/
@[specialize]
def stripBlock (P : LdePlan p) (C : @& ByteArray) (t : Nat) : Array ByteArray :=
  let T := P.cosetTables.getD (NTT.Transform.bitRevNat P.bits t) .empty
  stripColumns (stripLayersFrom p P.forwardTwiddles P.logH (1 - P.logH % 2)
    (stripScaled p P.forwardTwiddles T C P.logH)) (2 ^ P.logH)

end CompPoly.CPolynomial.NTTFast.Packed.Native
