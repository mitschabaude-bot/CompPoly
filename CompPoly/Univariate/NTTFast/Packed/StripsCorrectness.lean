/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Strips
public import CompPoly.Univariate.NTTFast.Packed.CosetLdeCorrectness
public import CompPoly.Univariate.NTTFast.Packed.QuadCells
public import CompPoly.Univariate.NTTFast.Packed.ButterflyLemmas
import all CompPoly.Univariate.NTTFast.Plan
import all CompPoly.Univariate.NTTFast.Packed.Strips
import all CompPoly.Univariate.NTTFast.Packed.Native
import CompPoly.Univariate.NTTFast.Packed.Unrolled
import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! # Correctness of the strip extension

A DIF pass over a strip is the scalar pass over the strip as one array, with every twiddle repeated
for the eight lanes (`expand8`), and that pass acts on each column, the strip's lane, as the
column's own pass (`lane8_butterflyDIFRadix4Blocks`). So a strip's transform is its columns'
transforms (`lane8_stripLayersField`); `StripBlocksCorrectness.lean` assembles the coset blocks.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-! ### Lanes -/

/-- Column `l` of a strip of `n` rows: entries `l, 8 + l, …, 8 (n - 1) + l`. -/
def lane8 [Zero R] (S : Array R) (n l : Nat) : Array R :=
  Array.ofFn (n := n) fun r ↦ S.getD (8 * r.val + l) 0

@[simp] theorem size_lane8 [Zero R] (S : Array R) (n l : Nat) : (lane8 S n l).size = n :=
  Array.size_ofFn

theorem getD_lane8 [Zero R] (S : Array R) (n l r : Nat) (hr : r < n) :
    (lane8 S n l).getD r 0 = S.getD (8 * r + l) 0 :=
  getD_ofFn_bounded _ r hr 0

/-- Every entry of `t` eight times in a row: a table of twiddles broadcast over the lanes. -/
def expand8 [Zero R] (t : Array R) : Array R :=
  Array.ofFn (n := 8 * t.size) fun i ↦ t.getD (i.val / 8) 0

theorem getD_expand8 [Zero R] (t : Array R) (i : Nat) :
    (expand8 t).getD i 0 = t.getD (i / 8) 0 := by
  by_cases h : i < 8 * t.size
  · exact getD_ofFn_bounded _ i h 0
  · have h1 : (expand8 t).size ≤ i := by
      simp only [expand8, Array.size_ofFn]
      omega
    have h2 : t.size ≤ i / 8 := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h1, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none h2]

/-- Division and remainder from a decomposition `x = d a + b`, `b < d`. -/
theorem div_mod_of_eq {x d a b : Nat} (hd : 0 < d) (hx : x = d * a + b) (hb : b < d) :
    x / d = a ∧ x % d = b :=
  (Nat.div_mod_unique hd).mpr ⟨by rw [hx]; omega, hb⟩

/-! ### Radix-four passes, pointwise -/

/-- Entry `k` of a radix-four DIF pass of quarter `q` over blocks of `4 q`: the output of quarter
`c` of butterfly `o` of block `b`, `k = 4 q b + q c + o`. -/
def quadPassValue [Field R] (th tl : Array R) (q : Nat) (a : Array R) (k : Nat) : R :=
  let base := k / (4 * q) * (4 * q)
  let o := k % q
  let x (c : Nat) := a.getD (base + c * q + o) 0
  let out := quadOutputs (th.getD o 0) (th.getD (o + q) 0) (tl.getD o 0) (x 0) (x 1) (x 2) (x 3)
  match k % (4 * q) / q with
  | 0 => out.1
  | 1 => out.2.1
  | 2 => out.2.2.1
  | _ => out.2.2.2

/-- The coordinates of entry `4 q b + q c + o` of a pass of quarter `q`. -/
theorem quadPass_coords (q b c o : Nat) (hq : 0 < q) (hc : c < 4) (ho : o < q) :
    (b * (4 * q) + (c * q + o)) / (4 * q) = b ∧ (b * (4 * q) + (c * q + o)) % q = o ∧
      (b * (4 * q) + (c * q + o)) % (4 * q) / q = c := by
  have h1 := div_mod_of_eq (x := b * (4 * q) + (c * q + o)) (d := 4 * q) (a := b)
    (b := c * q + o) (by omega) (by rw [Nat.mul_comm]) (by
      have : c * q + o < 4 * q := by
        have : c * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
        omega
      exact this)
  have h2 := div_mod_of_eq (x := c * q + o) (d := q) (a := c) (b := o) hq
    (by rw [Nat.mul_comm]) ho
  have h3 : (b * (4 * q) + (c * q + o)) % q = o := by
    rw [show b * (4 * q) + (c * q + o) = q * (4 * b + c) + o by ring]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt ho
  exact ⟨h1.1, h3, by rw [h1.2, h2.1]⟩

/-- Inside its block, a block's cells are the pass. -/
theorem quadValue_eq_quadPassValue [Field R] (th tl : Array R) (q b : Nat) (a : Array R)
    (hq : 0 < q) (c o : Nat) (hc : c < 4) (ho : o < q) :
    quadValue th tl q 0 (b * (4 * q)) (b * (4 * q) + q) (b * (4 * q) + 2 * q)
      (b * (4 * q) + 3 * q) q a (b * (4 * q) + (c * q + o)) =
      quadPassValue th tl q a (b * (4 * q) + (c * q + o)) := by
  obtain ⟨h1, h2, h3⟩ := quadPass_coords q b c o hq hc ho
  unfold quadValue quadPassValue quadAt
  simp only [h1, h2, h3, Nat.zero_add]
  interval_cases c
  · rw [ite_eq_left (by omega)]
    congr <;> omega
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    congr <;> omega
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    congr <;> omega
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega)]
    congr <;> omega

/-- Every entry of a pass from its coordinates `4 q b + q c + o`. -/
theorem quadPass_decomp (q k : Nat) (hq : 0 < q) :
    ∃ b c o, c < 4 ∧ o < q ∧ k = b * (4 * q) + (c * q + o) := by
  refine ⟨k / (4 * q), k % (4 * q) / q, k % (4 * q) % q, ?_, Nat.mod_lt _ hq, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hq]
    exact Nat.mod_lt _ (by omega)
  · have h1 := Nat.div_add_mod k (4 * q)
    have h2 := Nat.div_add_mod (k % (4 * q)) q
    rw [Nat.mul_comm (k / (4 * q)), Nat.mul_comm (k % (4 * q) / q)]
    omega

/-- A pass's entry reads its block only. -/
theorem quadPassValue_congr [Field R] (th tl : Array R) (q : Nat) (a a' : Array R) (hq : 0 < q)
    (b c o : Nat) (hc : c < 4) (ho : o < q)
    (h : ∀ i, b * (4 * q) ≤ i → i < b * (4 * q) + 4 * q → a.getD i 0 = a'.getD i 0) :
    quadPassValue th tl q a (b * (4 * q) + (c * q + o)) =
      quadPassValue th tl q a' (b * (4 * q) + (c * q + o)) := by
  obtain ⟨h1, h2, h3⟩ := quadPass_coords q b c o hq hc ho
  unfold quadPassValue
  simp only [h1, h2, h3]
  have hr (c' : Nat) (hc' : c' < 4) :
      a.getD (b * (4 * q) + c' * q + o) 0 = a'.getD (b * (4 * q) + c' * q + o) 0 := by
    have : c' * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
    exact h _ (by omega) (by omega)
  rw [hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide)]

/-- Outside its four quarters, a range of cells keeps the array. -/
theorem quadValue_outside [Field R] (th tl : Array R) (q j i0 i1 i2 i3 count : Nat) (a : Array R)
    (k : Nat) (hk : ¬(i0 ≤ k ∧ k < i0 + count) ∧ ¬(i1 ≤ k ∧ k < i1 + count) ∧
      ¬(i2 ≤ k ∧ k < i2 + count) ∧ ¬(i3 ≤ k ∧ k < i3 + count)) :
    quadValue th tl q j i0 i1 i2 i3 count a k = a.getD k 0 := by
  unfold quadValue
  rw [ite_eq_right hk.1, ite_eq_right hk.2.1, ite_eq_right hk.2.2.1, ite_eq_right hk.2.2.2]

/-- **A radix-four DIF pass pointwise**: blocks `block, …, blocks - 1` of quarter `q`. -/
theorem getD_butterflyDIFRadix4Blocks [Field R] (th tl : Array R) (q blocks : Nat) (hq : 0 < q)
    (block : Nat) (a : Array R) (ha : 4 * q * blocks ≤ a.size) (k : Nat) :
    (Plan.butterflyDIFRadix4Blocks th tl (4 * q) q blocks block a).getD k 0 =
      if block * (4 * q) ≤ k ∧ k < blocks * (4 * q) then quadPassValue th tl q a k
      else a.getD k 0 := by
  have e1 : (block + 1) * (4 * q) = block * (4 * q) + 4 * q := by ring
  have e2 : blocks * (4 * q) = 4 * q * blocks := by ring
  rw [Plan.butterflyDIFRadix4Blocks]
  split
  · rename_i hb
    have hbl : (block + 1) * (4 * q) ≤ blocks * (4 * q) := Nat.mul_le_mul_right _ hb
    have hsz : block * (4 * q) + 3 * q + (q - 0) ≤ a.size := by omega
    have hinner (i : Nat) := getD_butterflyDIFRadix4Inner th tl q 0 (block * (4 * q))
      (block * (4 * q) + q) (block * (4 * q) + 2 * q) (block * (4 * q) + 3 * q) a hsz
      (by omega) (by omega) (by omega) i
    rw [getD_butterflyDIFRadix4Blocks th tl q blocks hq (block + 1) _
      (by rw [Plan.size_butterflyDIFRadix4Inner]; exact ha) k]
    obtain ⟨b, c, o, hc, ho, rfl⟩ := quadPass_decomp q k hq
    have hcq : c * q + o < 4 * q := by
      have : c * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
      omega
    have e3 : (b + 1) * (4 * q) = b * (4 * q) + 4 * q := by ring
    by_cases hlt : b < block
    · have : (b + 1) * (4 * q) ≤ block * (4 * q) := Nat.mul_le_mul_right _ hlt
      rw [ite_eq_right (by omega), ite_eq_right (by omega), hinner,
        quadValue_outside _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    · by_cases heq : b = block
      · subst heq
        rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, hinner, Nat.sub_zero,
          quadValue_eq_quadPassValue _ _ _ _ _ hq c o hc ho]
      · have h1 : (block + 1) * (4 * q) ≤ b * (4 * q) := Nat.mul_le_mul_right _ (by omega)
        by_cases hin : b < blocks
        · have h2 : (b + 1) * (4 * q) ≤ blocks * (4 * q) := Nat.mul_le_mul_right _ hin
          rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega⟩]
          apply quadPassValue_congr _ _ _ _ _ hq b c o hc ho
          intro i hi1 hi2
          rw [hinner, Nat.sub_zero, quadValue_outside _ _ _ _ _ _ _ _ _ _ _ (by omega)]
        · have h2 : blocks * (4 * q) ≤ b * (4 * q) := Nat.mul_le_mul_right _ (by omega)
          rw [ite_eq_right (by omega), ite_eq_right (by omega), hinner, Nat.sub_zero,
            quadValue_outside _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  · rename_i hb
    have : blocks * (4 * q) ≤ block * (4 * q) := Nat.mul_le_mul_right _ (by omega)
    rw [ite_eq_right (by omega)]
termination_by blocks - block
decreasing_by omega

/-- **A strip's radix-four pass is its columns' passes**: the pass of quarter `8 q` words with the
twiddles broadcast over the lanes acts on column `l` as the pass of quarter `q`. -/
theorem lane8_butterflyDIFRadix4Blocks [Field R] (th tl : Array R) (q blocks : Nat) (hq : 0 < q)
    (S : Array R) (hS : S.size = 8 * (4 * q * blocks)) (l : Nat) (hl : l < 8) :
    lane8 (Plan.butterflyDIFRadix4Blocks (expand8 th) (expand8 tl) (4 * (8 * q)) (8 * q) blocks 0
      S) (4 * q * blocks) l =
      Plan.butterflyDIFRadix4Blocks th tl (4 * q) q blocks 0 (lane8 S (4 * q * blocks) l) := by
  apply array_eq_of_getD _ _ (0 : R) (by
    rw [size_lane8, Plan.size_butterflyDIFRadix4Blocks, size_lane8])
  intro r
  by_cases hr : r < 4 * q * blocks
  · rw [getD_lane8 _ _ _ _ hr,
      getD_butterflyDIFRadix4Blocks _ _ _ _ (by omega) 0 S
        (by rw [hS, show 4 * (8 * q) * blocks = 8 * (4 * q * blocks) by ring]),
      getD_butterflyDIFRadix4Blocks _ _ _ _ hq 0 _ (by rw [size_lane8]) r]
    have e1 : blocks * (4 * (8 * q)) = 8 * (4 * q * blocks) := by ring
    have e2 : blocks * (4 * q) = 4 * q * blocks := by ring
    rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega⟩]
    obtain ⟨b, c, o, hc, ho, rfl⟩ := quadPass_decomp q r hq
    have e3 : 8 * (b * (4 * q) + (c * q + o)) + l =
        b * (4 * (8 * q)) + (c * (8 * q) + (8 * o + l)) := by ring
    rw [e3]
    obtain ⟨h1, h2, h3⟩ := quadPass_coords q b c o hq hc ho
    obtain ⟨g1, g2, g3⟩ := quadPass_coords (8 * q) b c (8 * o + l) (by omega) hc (by omega)
    unfold quadPassValue
    simp only [h1, h2, h3, g1, g2, g3, getD_expand8]
    have hrow (c' : Nat) (hc' : c' < 4) :
        S.getD (b * (4 * (8 * q)) + c' * (8 * q) + (8 * o + l)) 0 =
          (lane8 S (4 * q * blocks) l).getD (b * (4 * q) + c' * q + o) 0 := by
      have hb : b * (4 * q) + 4 * q ≤ 4 * q * blocks := by
        have := Nat.mul_le_mul_right (4 * q) (show b + 1 ≤ blocks by
          by_contra hne
          have : blocks * (4 * q) ≤ b * (4 * q) := Nat.mul_le_mul_right _ (by omega)
          omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have : c' * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
      rw [getD_lane8 _ _ _ _ (by omega)]
      congr 1
      ring
    rw [hrow 0 (by decide), hrow 1 (by decide), hrow 2 (by decide), hrow 3 (by decide)]
    have t1 : (8 * o + l) / 8 = o := by omega
    have t2 : (8 * o + l + 8 * q) / 8 = o + q := by omega
    rw [t1, t2]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_lane8]; omega),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [Plan.size_butterflyDIFRadix4Blocks, size_lane8]; omega)]

/-- **A strip's radix-two layer is its columns' layers**, for one block of half `8 half` words. -/
theorem lane8_butterflyDIFInner [Field R] (tw : Array R) (half : Nat) (S : Array R)
    (hS : S.size = 8 * (2 * half)) (l : Nat) (hl : l < 8) :
    lane8 (Plan.butterflyDIFInner (expand8 tw) (8 * half) 0 0 (8 * half) S) (2 * half) l =
      Plan.butterflyDIFInner tw half 0 0 half (lane8 S (2 * half) l) := by
  apply array_eq_of_getD _ _ (0 : R) (by
    rw [size_lane8, Plan.size_butterflyDIFInner, size_lane8])
  intro r
  by_cases hr : r < 2 * half
  · rw [getD_lane8 _ _ _ _ hr, getD_butterflyDIFInner _ _ _ _ _ _ (by omega) (by omega),
      getD_butterflyDIFInner _ _ _ _ _ _ (by rw [size_lane8]; omega) (by omega)]
    unfold difValue
    simp only [Nat.sub_zero, Nat.zero_add, getD_expand8]
    by_cases hlow : r < half
    · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega⟩, getD_lane8 _ _ _ _ hr,
        getD_lane8 _ _ _ _ (by omega)]
      congr 2
      omega
    · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, ite_eq_right (by omega),
        ite_eq_left ⟨by omega, by omega⟩, getD_lane8 _ _ _ _ hr, getD_lane8 _ _ _ _ (by omega)]
      have t1 : (8 * r + l - 8 * half) / 8 = r - half := by omega
      have t2 : 8 * r + l - 8 * half = 8 * (r - half) + l := by omega
      rw [t1, t2]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_lane8]; omega),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [Plan.size_butterflyDIFInner, size_lane8]; omega)]

/-! ### Row kernels -/

section Kernels
open Montgomery.Native32 (Mont32Field FastField)
open CompPoly.PackedRepr (encode size_encode_uint32)

variable {p : ℕ} [Mont32Field p]

set_option maxRecDepth 8192 in
/-- Field model of `Native.stripQuad`. -/
def stripQuadField (th tl : Array (FastField p)) (j j1 i0 i1 i2 i3 : USize)
    (b : Array (FastField p)) : Array (FastField p) :=
  stripQuad_fields%

set_option maxRecDepth 8192 in
/-- Field model of `Native.stripLast`. -/
def stripLastField (w1 : FastField p) (i0 i1 i2 i3 : USize) (b : Array (FastField p)) :
    Array (FastField p) :=
  stripLast_fields%

set_option maxRecDepth 8192 in
/-- Field model of `Native.stripPair`. -/
def stripPairField (tw : Array (FastField p)) (j i0 i1 : USize) (b : Array (FastField p)) :
    Array (FastField p) :=
  stripPair_fields%

/-- An eight-word store at word `i` into encoded field values splices the values in. -/
theorem Native.storeWords8_encode_row (a : Array (FastField p)) (i : USize)
    (hs : 4 * a.size < USize.size) (hi : i.toNat + 8 ≤ a.size)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FastField p) :
    Native.storeWords (encode a) (i * 4) 8 x0.val x1.val x2.val x3.val x4.val
      x5.val x6.val x7.val 0 0 0 0 0 0 0 0 =
      encode (splice8 a i.toNat x0 x1 x2 x3 x4 x5 x6 x7) := by
  rw [splice8_eq_splice _ _ _ _ _ _ _ _ _ _ hi]
  exact Native.storeWords8_encode a _ _ (Native.wordOffset_toNat' _ (by omega))
    (by rw [size_encode_fields]; exact hs) hi _ _ _ _ _ _ _ _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The radix-four strip row runs its field model. -/
theorem Native.stripQuad_encode (th tl a : Array (FastField p)) (j j1 i0 i1 i2 i3 : USize)
    (hr0 hr1 hr2 hr3 hb hwj hwj1 hth hwl htl) :
    (Native.stripQuad p (encode th) (encode tl) j j1 i0 i1 i2 i3 (encode a) hr0 hr1 hr2 hr3 hb
      hwj hwj1 hth hwl htl).1 = encode (stripQuadField th tl j j1 i0 i1 i2 i3 a) := by
  have hs : 4 * a.size < USize.size := by rwa [size_encode_fields] at hb
  rw [size_encode_fields] at hr0 hr1 hr2 hr3
  unfold Native.stripQuad
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ hb, Native.touchLast, Native.touch_eq]
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  simp (disch := ((try simp only [size_splice8]); omega))
    only [Native.storeWords8_encode_row]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The last radix-four strip pass on a block runs its field model. -/
theorem Native.stripLast_encode (w1 : FastField p) (a : Array (FastField p))
    (i0 i1 i2 i3 : USize) (hr0 hr1 hr2 hr3 hb) :
    (Native.stripLast p w1.val i0 i1 i2 i3 (encode a) hr0 hr1 hr2 hr3 hb).1 =
      encode (stripLastField w1 i0 i1 i2 i3 a) := by
  have hs : 4 * a.size < USize.size := by rwa [size_encode_fields] at hb
  rw [size_encode_fields] at hr0 hr1 hr2 hr3
  unfold Native.stripLast
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ hb, Native.touchLast, Native.touch_eq]
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  simp (disch := ((try simp only [size_splice8]); omega))
    only [Native.storeWords8_encode_row]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The radix-two strip row runs its field model. -/
theorem Native.stripPair_encode (tw a : Array (FastField p)) (j i0 i1 : USize)
    (hr0 hr1 hb hwj htw) :
    (Native.stripPair p (encode tw) j i0 i1 (encode a) hr0 hr1 hb hwj htw).1 =
      encode (stripPairField tw j i0 i1 a) := by
  have hs : 4 * a.size < USize.size := by rwa [size_encode_fields] at hb
  rw [size_encode_fields] at hr0 hr1
  unfold Native.stripPair
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ hb, Native.touchLast, Native.touch_eq]
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  simp (disch := ((try simp only [size_splice8]); omega))
    only [Native.storeWords8_encode_row]
  rfl

theorem div8_add (j o : Nat) (ho : o < 8) : (8 * j + o) / 8 = j := by omega

theorem div8_add_add (j o q : Nat) (ho : o < 8) : (8 * j + o + 8 * q) / 8 = j + q := by omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The radix-four strip row's model is eight cells of the pass with broadcast twiddles. -/
theorem getD_stripQuadField (th tl a : Array (FastField p)) (q : Nat) (j j1 i0 i1 i2 i3 : USize)
    (hj1 : j1.toNat = j.toNat + q) (hs : i3.toNat + 8 ≤ a.size)
    (h01 : i0.toNat + 8 ≤ i1.toNat) (h12 : i1.toNat + 8 ≤ i2.toNat)
    (h23 : i2.toNat + 8 ≤ i3.toNat) (k : Nat) :
    (stripQuadField th tl j j1 i0 i1 i2 i3 a).getD k 0 =
      quadValue (expand8 th) (expand8 tl) (8 * q) (8 * j.toNat) i0.toNat i1.toNat i2.toNat
        i3.toNat 8 a k := by
  unfold stripQuadField readField fieldAdd fieldSub fieldMul quadValue quadAt quadOutputs
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide),
    Native.usize_numeral 4 (by decide), Native.usize_numeral 5 (by decide),
    Native.usize_numeral 6 (by decide), Native.usize_numeral 7 (by decide), hj1,
    Nat.add_zero, getD_expand8]
  by_cases hk3 : i3.toNat ≤ k ∧ k < i3.toNat + 8
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i3.toNat + o := ⟨k - i3.toNat, by omega, by omega⟩
    rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by simp only [size_splice8]; omega) _ _ hk3,
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left hk3, Nat.add_sub_cancel_left]
    try simp only [div8_add _ _ ho, div8_add_add _ _ _ ho]
    interval_cases o <;> rfl
  · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    by_cases hk2 : i2.toNat ≤ k ∧ k < i2.toNat + 8
    · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i2.toNat + o := ⟨k - i2.toNat, by omega, by omega⟩
      rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by simp only [size_splice8]; omega) _ _ hk2,
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hk2,
        Nat.add_sub_cancel_left]
      try simp only [div8_add _ _ ho, div8_add_add _ _ _ ho]
      interval_cases o <;> rfl
    · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
      by_cases hk1 : i1.toNat ≤ k ∧ k < i1.toNat + 8
      · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i1.toNat + o :=
          ⟨k - i1.toNat, by omega, by omega⟩
        rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by simp only [size_splice8]; omega) _ _ hk1,
          ite_eq_right (by omega), ite_eq_left hk1, Nat.add_sub_cancel_left]
        try simp only [div8_add _ _ ho]
        interval_cases o <;> rfl
      · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
        by_cases hk0 : i0.toNat ≤ k ∧ k < i0.toNat + 8
        · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i0.toNat + o :=
            ⟨k - i0.toNat, by omega, by omega⟩
          rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by omega) _ _ hk0, ite_eq_left hk0,
            Nat.add_sub_cancel_left]
          interval_cases o <;> rfl
        · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega), ite_eq_right hk0,
            ite_eq_right hk1, ite_eq_right hk2, ite_eq_right hk3]

/-- The radix-four strip row's model is eight cells of the pass with broadcast twiddles. -/
theorem stripQuadField_eq_quadCells (th tl a : Array (FastField p)) (q : Nat)
    (j j1 i0 i1 i2 i3 : USize) (hj1 : j1.toNat = j.toNat + q) (hs : i3.toNat + 8 ≤ a.size)
    (h01 : i0.toNat + 8 ≤ i1.toNat) (h12 : i1.toNat + 8 ≤ i2.toNat)
    (h23 : i2.toNat + 8 ≤ i3.toNat) :
    stripQuadField th tl j j1 i0 i1 i2 i3 a =
      quadCells (expand8 th) (expand8 tl) (8 * q) (8 * j.toNat) i0.toNat i1.toNat i2.toNat
        i3.toNat a 8 := by
  apply array_eq_of_getD _ _ (0 : FastField p)
  · rw [size_quadCells]
    unfold stripQuadField
    simp only [size_splice8]
  · intro k
    rw [getD_stripQuadField th tl a q j j1 i0 i1 i2 i3 hj1 hs h01 h12 h23,
      getD_quadCells _ _ _ _ _ _ _ _ a 8 hs h01 h12 h23]

theorem div8_of_lt (o : Nat) (ho : o < 8) : o / 8 = 0 := by omega

theorem div8_add8 (o : Nat) (ho : o < 8) : (o + 8) / 8 = 1 := by omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The last pass's model on a block is the pass's four cells with twiddles `1`, `w1`, `1`. -/
theorem getD_stripLastField (th tl a : Array (FastField p)) (i0 i1 i2 i3 : USize)
    (hs : i3.toNat + 8 ≤ a.size) (h01 : i0.toNat + 8 ≤ i1.toNat) (h12 : i1.toNat + 8 ≤ i2.toNat)
    (h23 : i2.toNat + 8 ≤ i3.toNat) (h1 : th.getD 0 0 = 1) (hl : tl.getD 0 0 = 1) (k : Nat) :
    (stripLastField (th.getD 1 0) i0 i1 i2 i3 a).getD k 0 =
      quadValue (expand8 th) (expand8 tl) 8 0 i0.toNat i1.toNat i2.toNat i3.toNat 8 a k := by
  unfold stripLastField readField fieldAdd fieldSub fieldMul quadValue quadAt quadOutputs
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide),
    Native.usize_numeral 4 (by decide), Native.usize_numeral 5 (by decide),
    Native.usize_numeral 6 (by decide), Native.usize_numeral 7 (by decide),
    Nat.add_zero, Nat.zero_add, getD_expand8]
  by_cases hk3 : i3.toNat ≤ k ∧ k < i3.toNat + 8
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i3.toNat + o := ⟨k - i3.toNat, by omega, by omega⟩
    rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by simp only [size_splice8]; omega) _ _ hk3,
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left hk3]
    simp only [Nat.add_sub_cancel_left, div8_of_lt _ ho, div8_add8 _ ho, h1, hl, one_mul]
    interval_cases o <;> rfl
  · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    by_cases hk2 : i2.toNat ≤ k ∧ k < i2.toNat + 8
    · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i2.toNat + o := ⟨k - i2.toNat, by omega, by omega⟩
      rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by simp only [size_splice8]; omega) _ _ hk2,
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hk2,
        Nat.add_sub_cancel_left]
      try simp only [div8_of_lt _ ho, div8_add8 _ ho, h1, one_mul]
      interval_cases o <;> rfl
    · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
      by_cases hk1 : i1.toNat ≤ k ∧ k < i1.toNat + 8
      · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i1.toNat + o :=
          ⟨k - i1.toNat, by omega, by omega⟩
        rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by simp only [size_splice8]; omega) _ _ hk1,
          ite_eq_right (by omega), ite_eq_left hk1, Nat.add_sub_cancel_left]
        try simp only [div8_of_lt _ ho, hl, one_mul]
        interval_cases o <;> rfl
      · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
        by_cases hk0 : i0.toNat ≤ k ∧ k < i0.toNat + 8
        · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i0.toNat + o :=
            ⟨k - i0.toNat, by omega, by omega⟩
          rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by omega) _ _ hk0, ite_eq_left hk0,
            Nat.add_sub_cancel_left]
          interval_cases o <;> rfl
        · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega), ite_eq_right hk0,
            ite_eq_right hk1, ite_eq_right hk2, ite_eq_right hk3]

/-- The last pass's model on a block is its four cells. -/
theorem stripLastField_eq_quadCells (th tl a : Array (FastField p)) (i0 i1 i2 i3 : USize)
    (hs : i3.toNat + 8 ≤ a.size) (h01 : i0.toNat + 8 ≤ i1.toNat) (h12 : i1.toNat + 8 ≤ i2.toNat)
    (h23 : i2.toNat + 8 ≤ i3.toNat) (h1 : th.getD 0 0 = 1) (hl : tl.getD 0 0 = 1) :
    stripLastField (th.getD 1 0) i0 i1 i2 i3 a =
      quadCells (expand8 th) (expand8 tl) 8 0 i0.toNat i1.toNat i2.toNat i3.toNat a 8 := by
  apply array_eq_of_getD _ _ (0 : FastField p)
  · rw [size_quadCells]
    unfold stripLastField
    simp only [size_splice8]
  · intro k
    rw [getD_stripLastField th tl a i0 i1 i2 i3 hs h01 h12 h23 h1 hl,
      getD_quadCells _ _ _ _ _ _ _ _ a 8 hs h01 h12 h23]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The radix-two strip row's model is eight butterflies of the layer with broadcast twiddles. -/
theorem getD_stripPairField (tw a : Array (FastField p)) (j i0 i1 : USize)
    (hs : i1.toNat + 8 ≤ a.size) (h01 : i0.toNat + 8 ≤ i1.toNat) (k : Nat) :
    (stripPairField tw j i0 i1 a).getD k 0 =
      difValue (expand8 tw) (8 * j.toNat) i0.toNat i1.toNat 8 a k := by
  unfold stripPairField readField fieldAdd fieldSub fieldMul difValue
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide),
    Native.usize_numeral 4 (by decide), Native.usize_numeral 5 (by decide),
    Native.usize_numeral 6 (by decide), Native.usize_numeral 7 (by decide),
    Nat.add_zero, getD_expand8]
  by_cases hk1 : i1.toNat ≤ k ∧ k < i1.toNat + 8
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i1.toNat + o := ⟨k - i1.toNat, by omega, by omega⟩
    rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by simp only [size_splice8]; omega) _ _ hk1,
      ite_eq_right (by omega), ite_eq_left hk1, Nat.add_sub_cancel_left]
    try simp only [div8_add _ _ ho]
    interval_cases o <;> rfl
  · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    by_cases hk0 : i0.toNat ≤ k ∧ k < i0.toNat + 8
    · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i0.toNat + o := ⟨k - i0.toNat, by omega, by omega⟩
      rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by omega) _ _ hk0, ite_eq_left hk0,
        Nat.add_sub_cancel_left]
      interval_cases o <;> rfl
    · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega), ite_eq_right hk0,
        ite_eq_right hk1]

/-- The radix-two strip row's model is eight butterflies of the layer with broadcast twiddles. -/
theorem stripPairField_eq (tw a : Array (FastField p)) (j i0 i1 : USize)
    (hs : i1.toNat + 8 ≤ a.size) (h01 : i0.toNat + 8 ≤ i1.toNat) :
    stripPairField tw j i0 i1 a =
      Plan.butterflyDIFInner (expand8 tw) (8 * j.toNat + 8) (8 * j.toNat) i0.toNat i1.toNat a := by
  apply array_eq_of_getD _ _ (0 : FastField p)
  · rw [Plan.size_butterflyDIFInner]
    unfold stripPairField
    simp only [size_splice8]
  · intro k
    rw [getD_stripPairField tw a j i0 i1 hs h01,
      getD_butterflyDIFInner _ _ _ _ _ a (by omega) (by omega), Nat.add_sub_cancel_left]

/-! ### Passes -/

/-- The radix-four row loop depends only on the buffer's value. -/
theorem Native.stripQuadRows_congr {th tl : ByteArray} {qq : USize} {n : Nat} {j j1 i0 : USize}
    {b b' : ByteArray} (h) (e : b = b') :
    Native.stripQuadRows p th tl qq n j j1 i0 b h =
      Native.stripQuadRows p th tl qq n j j1 i0 b' (e ▸ h) := by
  subst e
  rfl

/-- The radix-four row loop runs `8 n` cells of the pass with broadcast twiddles. -/
theorem Native.stripQuadRows_encode (th tl : Array (FastField p)) (q : Nat) (qq : USize)
    (hqq : qq.toNat = 8 * q) (hq : 0 < q) :
    ∀ (n : Nat) (j j1 i0 : USize) (a : Array (FastField p)) (h), j1.toNat = j.toNat + q →
    Native.stripQuadRows p (encode th) (encode tl) qq n j j1 i0 (encode a) h =
      encode (quadCells (expand8 th) (expand8 tl) (8 * q) (8 * j.toNat) i0.toNat
        (i0.toNat + 8 * q) (i0.toNat + 2 * (8 * q)) (i0.toNat + 3 * (8 * q)) a (8 * n)) := by
  intro n
  induction n with
  | zero => intro j j1 i0 a h _; rfl
  | succ n ih =>
    intro j j1 i0 a h hj1
    obtain ⟨hb, hs, -⟩ := h
    have hsz : 4 * a.size < USize.size := by rwa [size_encode_fields] at hs
    rw [size_encode_fields] at hb
    have h1 : (i0 + qq).toNat = i0.toNat + 8 * q := by
      rw [Native.usize_add_toNat _ _ (by omega), hqq]
    have h2 : (i0 + 2 * qq).toNat = i0.toNat + 2 * (8 * q) := by
      rw [Native.usize_add_toNat _ _
        (by rw [Native.usize_mul_small 2 qq (by decide) (by omega)]; omega),
        Native.usize_mul_small 2 qq (by decide) (by omega), hqq]
    have h3 : (i0 + 3 * qq).toNat = i0.toNat + 3 * (8 * q) := by
      rw [Native.usize_add_toNat _ _
        (by rw [Native.usize_mul_small 3 qq (by decide) (by omega)]; omega),
        Native.usize_mul_small 3 qq (by decide) (by omega), hqq]
    have hi8 : (i0 + 8).toNat = i0.toNat + 8 := by
      rw [Native.usize_add_toNat _ _ (by rw [Native.usize_numeral 8 (by decide)]; omega),
        Native.usize_numeral 8 (by decide)]
    have hj : (j + 1).toNat = j.toNat + 1 := by
      rw [Native.usize_add_toNat _ _ (by rw [Native.usize_numeral 1 (by decide)]; omega),
        Native.usize_numeral 1 (by decide)]
    have hj1' : (j1 + 1).toNat = j1.toNat + 1 := by
      rw [Native.usize_add_toNat _ _ (by rw [Native.usize_numeral 1 (by decide)]; omega),
        Native.usize_numeral 1 (by decide)]
    rw [Native.stripQuadRows]
    rw [Native.stripQuadRows_congr _ ((Native.stripQuad_encode th tl a _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _).trans (congrArg encode (stripQuadField_eq_quadCells th tl a q j j1 i0 _ _ _ hj1
        (by rw [h3]; omega) (by rw [h1]; omega) (by rw [h1, h2]; omega)
        (by rw [h2, h3]; omega))))]
    rw [ih _ _ _ _ _ (by rw [hj, hj1', hj1]; omega), hj, hi8, h1, h2, h3,
      show 8 * (n + 1) = 8 + 8 * n by ring, quadCells_add,
      show 8 * (j.toNat + 1) = 8 * j.toNat + 8 by ring,
      show i0.toNat + 8 + 8 * q = i0.toNat + 8 * q + 8 by ring,
      show i0.toNat + 8 + 2 * (8 * q) = i0.toNat + 2 * (8 * q) + 8 by ring,
      show i0.toNat + 8 + 3 * (8 * q) = i0.toNat + 3 * (8 * q) + 8 by ring]

/-- The radix-four block loop depends only on the buffer's value. -/
theorem Native.stripQuadBlocks_congr {th tl : ByteArray} {q : USize} {blocks : Nat} {base : USize}
    {b b' : ByteArray} (h) (e : b = b') :
    Native.stripQuadBlocks p th tl q blocks base b h =
      Native.stripQuadBlocks p th tl q blocks base b' (e ▸ h) := by
  subst e
  rfl

/-- The radix-four block loop runs blocks `b0, …, b0 + blocks - 1` of the pass with broadcast
twiddles. -/
theorem Native.stripQuadBlocks_encode (th tl : Array (FastField p)) (q : Nat) (qU : USize)
    (hqU : qU.toNat = q) (hq : 0 < q) :
    ∀ (blocks b0 : Nat) (base : USize) (a : Array (FastField p)) (h),
    base.toNat = b0 * (4 * (8 * q)) →
    Native.stripQuadBlocks p (encode th) (encode tl) qU blocks base (encode a) h =
      encode (Plan.butterflyDIFRadix4Blocks (expand8 th) (expand8 tl) (4 * (8 * q)) (8 * q)
        (b0 + blocks) b0 a) := by
  intro blocks
  induction blocks with
  | zero =>
    intro b0 base a h _
    rw [Native.stripQuadBlocks, Plan.butterflyDIFRadix4Blocks]
    simp only [Nat.add_zero, Nat.lt_irrefl, ↓reduceIte]
  | succ blocks ih =>
    intro b0 base a h hbase
    have h8 : (8 * qU).toNat = 8 * q := by
      rw [Native.usize_mul_toNat 8 qU (by decide) (by
        have := h.2.1; rw [size_encode_fields] at this; have := h.1
        rw [size_encode_fields] at this
        have : 32 * qU.toNat ≤ 32 * qU.toNat * (blocks + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega), hqU]
    have h32 : (32 * qU).toNat = 32 * q := by
      rw [Native.usize_mul_toNat 32 qU (by decide) (by
        have := h.2.1; rw [size_encode_fields] at this; have := h.1
        rw [size_encode_fields] at this
        have : 32 * qU.toNat ≤ 32 * qU.toNat * (blocks + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega), hqU]
    have hn : (base + 32 * qU).toNat = (b0 + 1) * (4 * (8 * q)) := by
      rw [Native.usize_add_toNat _ _ (by
        rw [h32]
        have := h.2.1; rw [size_encode_fields] at this; have := h.1
        rw [size_encode_fields, hqU] at this
        have : 32 * q ≤ 32 * q * (blocks + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega), h32, hbase]
      ring
    rw [Native.stripQuadBlocks]
    rw [Native.stripQuadBlocks_congr _ (Native.stripQuadRows_encode th tl q (8 * qU) h8 hq
      qU.toNat 0 qU base a _ (by rw [USize.toNat_zero, hqU, Nat.zero_add]))]
    rw [ih (b0 + 1) _ _ _ hn, hqU]
    conv_rhs => rw [Plan.butterflyDIFRadix4Blocks]
    simp only [show b0 < b0 + (blocks + 1) by omega, ↓reduceIte]
    rw [show b0 + 1 + blocks = b0 + (blocks + 1) by omega, USize.toNat_zero, Nat.mul_zero,
      hbase, butterflyDIFRadix4Inner_eq_quadCells, Nat.sub_zero]

/-- The last pass's block loop depends only on the buffer's value. -/
theorem Native.stripLastBlocks_congr {w1 : UInt32} {blocks : Nat} {base : USize}
    {b b' : ByteArray} (h) (e : b = b') :
    Native.stripLastBlocks p w1 blocks base b h =
      Native.stripLastBlocks p w1 blocks base b' (e ▸ h) := by
  subst e
  rfl

/-- The last pass's block loop runs blocks `b0, …, b0 + blocks - 1` of the pass of quarter one
row, whose twiddle tables start with `1`. -/
theorem Native.stripLastBlocks_encode (th tl : Array (FastField p)) (h1 : th.getD 0 0 = 1)
    (hl : tl.getD 0 0 = 1) :
    ∀ (blocks b0 : Nat) (base : USize) (a : Array (FastField p)) (h), base.toNat = b0 * 32 →
    Native.stripLastBlocks p (th.getD 1 0).val blocks base (encode a) h =
      encode (Plan.butterflyDIFRadix4Blocks (expand8 th) (expand8 tl) (4 * (8 * 1)) (8 * 1)
        (b0 + blocks) b0 a) := by
  intro blocks
  induction blocks with
  | zero =>
    intro b0 base a h _
    rw [Native.stripLastBlocks, Plan.butterflyDIFRadix4Blocks]
    simp only [Nat.add_zero, Nat.lt_irrefl, ↓reduceIte]
  | succ blocks ih =>
    intro b0 base a h hbase
    obtain ⟨hb, hs⟩ := h
    have hsz : 4 * a.size < USize.size := by rwa [size_encode_fields] at hs
    rw [size_encode_fields] at hb
    have hc (o : Nat) (ho : o ≤ 32) : (base + OfNat.ofNat o).toNat = base.toNat + o := by
      rw [Native.usize_add_toNat _ _ (by rw [Native.usize_numeral o (by omega)]; omega),
        Native.usize_numeral o (by omega)]
    rw [Native.stripLastBlocks]
    rw [Native.stripLastBlocks_congr _ ((Native.stripLast_encode (th.getD 1 0) a _ _ _ _ _ _ _ _
      _).trans (congrArg encode (stripLastField_eq_quadCells th tl a _ _ _ _
        (by rw [hc 24 (by decide)]; omega)
        (by rw [hc 0 (by decide), hc 8 (by decide)])
        (by rw [hc 8 (by decide), hc 16 (by decide)])
        (by rw [hc 16 (by decide), hc 24 (by decide)]) h1 hl)))]
    rw [ih (b0 + 1) _ _ _ (by rw [hc 32 (by decide), hbase]; ring)]
    conv_rhs => rw [Plan.butterflyDIFRadix4Blocks]
    simp only [show b0 < b0 + (blocks + 1) by omega, ↓reduceIte]
    rw [show b0 + 1 + blocks = b0 + (blocks + 1) by omega, hc 0 (by decide), hc 8 (by decide),
      hc 16 (by decide), hc 24 (by decide), hbase, butterflyDIFRadix4Inner_eq_quadCells,
      Nat.sub_zero]
    simp only [Nat.mul_one, Nat.reduceMul, Nat.add_zero]

/-- **A radix-four pass over a strip** is the pass with broadcast twiddles, for tables of the
pass's sizes; the last pass, of quarter one row, takes tables that start with `1`. -/
theorem Native.stripRadix4_encode (th tl a : Array (FastField p)) (q blocks : Nat) (hq : 0 < q)
    (ha : a.size = 32 * q * blocks) (hth : 2 * q ≤ th.size) (htl : q ≤ tl.size)
    (hs : 4 * a.size < USize.size) (hts : 4 * th.size < USize.size)
    (htls : 4 * tl.size < USize.size) (hone : q = 1 → th.getD 0 0 = 1 ∧ tl.getD 0 0 = 1) :
    Native.stripRadix4 p (encode th) (encode tl) q blocks (encode a) =
      encode (Plan.butterflyDIFRadix4Blocks (expand8 th) (expand8 tl) (4 * (8 * q)) (8 * q)
        blocks 0 a) := by
  unfold Native.stripRadix4
  rw [dite_eq_left_of_eq_true (eq_true (by simp only [size_encode_fields]; omega))]
  split
  · rename_i h1
    subst h1
    rw [Native.read_encode _ _ (by rw [size_encode_fields]; exact hts) (by omega)]
    exact (Native.stripLastBlocks_encode th tl (hone rfl).1 (hone rfl).2 blocks 0 0 a _
      (by rw [USize.toNat_zero])).trans (by rw [Nat.zero_add])
  · exact (Native.stripQuadBlocks_encode th tl q _ USize.toNat_ofNatLT hq blocks 0 0 a _
      (by rw [USize.toNat_zero, Nat.zero_mul])).trans (by rw [Nat.zero_add])

/-- The radix-two row loop depends only on the buffer's value. -/
theorem Native.stripPairRows_congr {tw : ByteArray} {qq : USize} {n : Nat} {j i0 : USize}
    {b b' : ByteArray} (h) (e : b = b') :
    Native.stripPairRows p tw qq n j i0 b h = Native.stripPairRows p tw qq n j i0 b' (e ▸ h) := by
  subst e
  rfl

/-- The radix-two row loop runs `8 n` butterflies of the layer with broadcast twiddles. -/
theorem Native.stripPairRows_encode (tw : Array (FastField p)) (qq : USize) (hqq : 8 ≤ qq.toNat) :
    ∀ (n : Nat) (j i0 : USize) (a : Array (FastField p)) (h),
    Native.stripPairRows p (encode tw) qq n j i0 (encode a) h =
      encode (Plan.butterflyDIFInner (expand8 tw) (8 * (j.toNat + n)) (8 * j.toNat) i0.toNat
        (i0.toNat + qq.toNat) a) := by
  intro n
  induction n with
  | zero =>
    intro j i0 a h
    rw [Native.stripPairRows, Nat.add_zero, Plan.butterflyDIFInner]
    simp only [Nat.lt_irrefl, ↓reduceIte]
  | succ n ih =>
    intro j i0 a h
    obtain ⟨hb, hs, -⟩ := h
    have hsz : 4 * a.size < USize.size := by rwa [size_encode_fields] at hs
    rw [size_encode_fields] at hb
    have h1 : (i0 + qq).toNat = i0.toNat + qq.toNat := Native.usize_add_toNat _ _ (by omega)
    have hi8 : (i0 + 8).toNat = i0.toNat + 8 := by
      rw [Native.usize_add_toNat _ _ (by rw [Native.usize_numeral 8 (by decide)]; omega),
        Native.usize_numeral 8 (by decide)]
    have hj : (j + 1).toNat = j.toNat + 1 := by
      rw [Native.usize_add_toNat _ _ (by rw [Native.usize_numeral 1 (by decide)]; omega),
        Native.usize_numeral 1 (by decide)]
    rw [Native.stripPairRows]
    rw [Native.stripPairRows_congr _ ((Native.stripPair_encode tw a _ _ _ _ _ _ _ _).trans
      (congrArg encode (stripPairField_eq tw a j i0 _ (by rw [h1]; omega)
        (by rw [h1]; omega))))]
    rw [ih, hj, hi8, h1, butterflyDIFInner_split (expand8 tw) (8 * (j.toNat + (n + 1))) 8
      (8 * j.toNat) i0.toNat (i0.toNat + qq.toNat) a (by omega)]
    rw [show 8 * (j.toNat + 1 + n) = 8 * (j.toNat + (n + 1)) by ring,
      show 8 * (j.toNat + 1) = 8 * j.toNat + 8 by ring,
      show i0.toNat + 8 + qq.toNat = i0.toNat + qq.toNat + 8 by ring]

/-- **A strip's radix-two layer** is the layer with broadcast twiddles. -/
theorem Native.stripRadix2_encode (tw a : Array (FastField p)) (half : Nat) (hh : 0 < half)
    (ha : a.size = 16 * half) (htw : half ≤ tw.size) (hs : 4 * a.size < USize.size)
    (hts : 4 * tw.size < USize.size) :
    Native.stripRadix2 p (encode tw) half (encode a) =
      encode (Plan.butterflyDIFInner (expand8 tw) (8 * half) 0 0 (8 * half) a) := by
  unfold Native.stripRadix2
  rw [dite_eq_left_of_eq_true (eq_true (by simp only [size_encode_fields]; omega))]
  rw [Native.stripPairRows_encode tw _ (by rw [USize.toNat_ofNatLT]; omega)]
  simp only [USize.toNat_zero, USize.toNat_ofNatLT, Nat.zero_add, Nat.mul_zero]

/-! ### Transforms -/

/-- The radix-four DIF passes `start, …` of a `2 ^ m`-point transform with twiddle tables `tw`:
those of `fieldLayers`. -/
def difPasses (tw : Array (Array (FastField p))) (m start : Nat) (X : Array (FastField p)) :
    Array (FastField p) :=
  (List.range' start (m / 2 - start)).foldl (fun b pass ↦
    let high := m - 1 - m % 2 - 2 * pass
    let q := 2 ^ (high - 1)
    Plan.butterflyDIFRadix4Blocks (tw.getD high #[]) (tw.getD (high - 1) #[]) (4 * q) q
      (2 ^ m / (4 * q)) 0 b) X

/-- The same passes over a strip, with the twiddles broadcast over the lanes. -/
def stripPasses (tw : Array (Array (FastField p))) (m start : Nat) (S : Array (FastField p)) :
    Array (FastField p) :=
  (List.range' start (m / 2 - start)).foldl (fun b pass ↦
    let high := m - 1 - m % 2 - 2 * pass
    let q := 2 ^ (high - 1)
    Plan.butterflyDIFRadix4Blocks (expand8 (tw.getD high #[])) (expand8 (tw.getD (high - 1) #[]))
      (4 * (8 * q)) (8 * q) (2 ^ m / (4 * q)) 0 b) S

/-- A pass's quarter divides the transform into whole blocks. -/
theorem pass_blocks (m pass : Nat) (hp : pass < m / 2) :
    4 * 2 ^ (m - 1 - m % 2 - 2 * pass - 1) * (2 ^ m / (4 * 2 ^ (m - 1 - m % 2 - 2 * pass - 1))) =
      2 ^ m := by
  have hd : 4 * 2 ^ (m - 1 - m % 2 - 2 * pass - 1) ∣ 2 ^ m := by
    rw [show 4 * 2 ^ (m - 1 - m % 2 - 2 * pass - 1) = 2 ^ (m - 1 - m % 2 - 2 * pass - 1 + 2) by
      rw [Nat.pow_add]; ring]
    exact Nat.pow_dvd_pow 2 (by omega)
  exact Nat.mul_div_cancel' hd

@[simp] theorem size_stripPasses (tw : Array (Array (FastField p))) (m start : Nat)
    (S : Array (FastField p)) : (stripPasses tw m start S).size = S.size := by
  unfold stripPasses
  apply foldl_invariant _ (fun b : Array (FastField p) ↦ b.size = S.size) _ _ S rfl
  intro _ _ b hb
  rw [Plan.size_butterflyDIFRadix4Blocks, hb]

@[simp] theorem size_difPasses (tw : Array (Array (FastField p))) (m start : Nat)
    (X : Array (FastField p)) : (difPasses tw m start X).size = X.size := by
  unfold difPasses
  apply foldl_invariant _ (fun b : Array (FastField p) ↦ b.size = X.size) _ _ X rfl
  intro _ _ b hb
  rw [Plan.size_butterflyDIFRadix4Blocks, hb]

/-- **A strip's passes are its columns' passes.** -/
theorem lane8_stripPasses (tw : Array (Array (FastField p))) (m start : Nat)
    (S : Array (FastField p)) (hS : S.size = 8 * 2 ^ m) (l : Nat) (hl : l < 8) :
    lane8 (stripPasses tw m start S) (2 ^ m) l = difPasses tw m start (lane8 S (2 ^ m) l) := by
  unfold stripPasses difPasses
  generalize hL : List.range' start (m / 2 - start) = L
  have hmem : ∀ pass ∈ L, pass < m / 2 := by
    intro pass hp
    rw [← hL, List.mem_range'_1] at hp
    omega
  clear hL
  induction L generalizing S with
  | nil => rfl
  | cons pass L ih =>
    simp only [List.foldl_cons]
    have hp := hmem pass List.mem_cons_self
    have hq : 0 < 2 ^ (m - 1 - m % 2 - 2 * pass - 1) := Nat.two_pow_pos _
    have key := lane8_butterflyDIFRadix4Blocks (tw.getD (m - 1 - m % 2 - 2 * pass) #[])
      (tw.getD (m - 1 - m % 2 - 2 * pass - 1) #[]) _ _ hq S (by rw [hS, pass_blocks m pass hp]) l hl
    rw [pass_blocks m pass hp] at key
    rw [← key]
    exact ih _ (by rw [Plan.size_butterflyDIFRadix4Blocks, hS])
      (fun x hx ↦ hmem x (List.mem_cons_of_mem pass hx))

/-- **A strip's passes on packed words** are its field passes, for twiddle tables of the
transform's sizes that start with `1`. -/
theorem Native.stripLayersFrom_encode (tw : Array (Array (FastField p))) (m start : Nat)
    (htw : TwiddleSizes m tw) (hone : TwiddleOnes m tw) (S : Array (FastField p))
    (hS : S.size = 8 * 2 ^ m) (hu : 4 * (8 * 2 ^ m) < USize.size) :
    Native.stripLayersFrom p (tw.map encode) m start (encode S) =
      encode (stripPasses tw m start S) := by
  unfold Native.stripLayersFrom stripPasses
  generalize hL : List.range' start (m / 2 - start) = L
  have hmem : ∀ pass ∈ L, pass < m / 2 := by
    intro pass hp
    rw [← hL, List.mem_range'_1] at hp
    omega
  clear hL
  induction L generalizing S with
  | nil => rfl
  | cons pass L ih =>
    simp only [List.foldl_cons]
    have hp := hmem pass List.mem_cons_self
    have hq : 0 < 2 ^ (m - 1 - m % 2 - 2 * pass - 1) := Nat.two_pow_pos _
    have hhigh : m - 1 - m % 2 - 2 * pass < m := by omega
    have hsz1 := htw _ hhigh
    have hsz0 := htw (m - 1 - m % 2 - 2 * pass - 1) (by omega)
    have h2 : 2 ^ (m - 1 - m % 2 - 2 * pass) = 2 * 2 ^ (m - 1 - m % 2 - 2 * pass - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hmono : 2 ^ (m - 1 - m % 2 - 2 * pass) ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [getD_map_encode, getD_map_encode, Native.stripRadix4_encode _ _ S _ _ hq
      (by rw [hS]; conv_lhs => rw [← pass_blocks m pass hp]
          ring)
      (by rw [hsz1, h2]) (by rw [hsz0]) (by omega) (by rw [hsz1]; omega) (by rw [hsz0]; omega)
      (fun h1 ↦ ⟨hone _ hhigh, by
        have : m - 1 - m % 2 - 2 * pass - 1 = 0 := by
          have := Nat.pow_right_injective (le_refl 2) (show 2 ^ (m - 1 - m % 2 - 2 * pass - 1) =
            2 ^ 0 from h1)
          exact this
        rw [this]
        exact hone 0 (by omega)⟩)]
    exact ih _ (by rw [Plan.size_butterflyDIFRadix4Blocks, hS])
      (fun x hx ↦ hmem x (List.mem_cons_of_mem pass hx))

/-- `fieldLayers` is its first layers, then the radix-four passes. -/
theorem fieldLayers_eq_difPasses (tw : Array (Array (FastField p))) (m : Nat)
    (X : Array (FastField p)) :
    fieldLayers tw m (m / 2) X = difPasses tw m 0 (if m % 2 = 1 then
      Plan.butterflyDIFInner (tw.getD (m - 1) #[]) (2 ^ (m - 1)) 0 0 (2 ^ (m - 1)) X else X) := by
  unfold fieldLayers difPasses
  rw [List.range_eq_range', Nat.sub_zero]

/-- The passes from `start` are the pass `start`, then the passes after it. -/
theorem difPasses_succ (tw : Array (Array (FastField p))) (m start : Nat) (h : start < m / 2)
    (X : Array (FastField p)) :
    difPasses tw m start X = difPasses tw m (start + 1)
      (Plan.butterflyDIFRadix4Blocks (tw.getD (m - 1 - m % 2 - 2 * start) #[])
        (tw.getD (m - 1 - m % 2 - 2 * start - 1) #[]) (4 * 2 ^ (m - 1 - m % 2 - 2 * start - 1))
        (2 ^ (m - 1 - m % 2 - 2 * start - 1)) (2 ^ m / (4 * 2 ^ (m - 1 - m % 2 - 2 * start - 1)))
        0 X) := by
  unfold difPasses
  rw [show m / 2 - start = (m / 2 - (start + 1)) + 1 by omega, List.range'_succ,
    List.foldl_cons]

/-- A strip's first layers and passes, the twiddle tables `tw` broadcast over the lanes: the field
semantics of `Native.stripLayers`. -/
def stripLayersField (tw : Array (Array (FastField p))) (m : Nat) (S : Array (FastField p)) :
    Array (FastField p) :=
  stripPasses tw m 0 (if m % 2 = 1 then
    Plan.butterflyDIFInner (expand8 (tw.getD (m - 1) #[])) (8 * 2 ^ (m - 1)) 0 0
      (8 * 2 ^ (m - 1)) S else S)

/-- **A strip's DIF transform on packed words** is its field semantics. -/
theorem Native.stripLayers_encode (tw : Array (Array (FastField p))) (m : Nat)
    (htw : TwiddleSizes m tw) (hone : TwiddleOnes m tw) (S : Array (FastField p))
    (hS : S.size = 8 * 2 ^ m) (hu : 4 * (8 * 2 ^ m) < USize.size) :
    Native.stripLayers p (tw.map encode) m (encode S) = encode (stripLayersField tw m S) := by
  unfold Native.stripLayers stripLayersField
  split
  · rename_i hm
    have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    rw [getD_map_encode, Native.stripRadix2_encode _ S _ (Nat.two_pow_pos _) (by rw [hS, h2]; ring)
      (by rw [htw _ (by omega)]) (by omega) (by rw [htw _ (by omega)]; omega)]
    exact Native.stripLayersFrom_encode tw m 0 htw hone _
      (by rw [Plan.size_butterflyDIFInner, hS]) hu
  · exact Native.stripLayersFrom_encode tw m 0 htw hone S hS hu

/-- **A strip's DIF transform is its columns' transforms**: column `l` of it is the DIF output,
the DFT in bit-reversed order, of column `l`. -/
theorem lane8_stripLayersField (D : NTT.Domain (FastField p)) (S : Array (FastField p))
    (hS : S.size = 8 * 2 ^ D.logN) (l : Nat) (hl : l < 8) :
    lane8 (stripLayersField (Plan.twiddleTable D) D.logN S) (2 ^ D.logN) l =
      difSpec D (lane8 S (2 ^ D.logN) l) := by
  unfold stripLayersField
  rw [lane8_stripPasses _ _ _ _ (by split <;> simp only [Plan.size_butterflyDIFInner, hS]) l hl,
    ← planStages_eq_difSpec D (lane8 S (2 ^ D.logN) l) (size_lane8 _ _ _),
    ← fieldLayers_eq D _ (lane8 S (2 ^ D.logN) l) (size_lane8 _ _ _), fieldLayers_eq_difPasses]
  congr 1
  split
  · rename_i hm
    have h2 : 2 ^ D.logN = 2 * 2 ^ (D.logN - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    have key := lane8_butterflyDIFInner ((Plan.twiddleTable D).getD (D.logN - 1) #[])
      (2 ^ (D.logN - 1)) S (by rw [hS, h2]) l hl
    rw [← h2] at key
    exact key
  · rfl

end Kernels

end CompPoly.CPolynomial.NTTFast.Packed
