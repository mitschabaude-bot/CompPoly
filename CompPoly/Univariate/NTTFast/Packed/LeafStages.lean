/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Expressions
public import CompPoly.Univariate.NTTFast.Packed.LeafLayers
public import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
import CompPoly.Univariate.NTTFast.Packed.Unrolled
import Mathlib.Tactic.IntervalCases

/-! # The final DIF layers one at a time

The stage kernels run each of the four final DIF layers over all sixteen-word blocks of a leaf
before the next, each block stored as two halves of eight words. The second and third stages store
their sums in a block's first half and their products in its second, so that a vector holds sums or
products only: their blocks are laid out by `swap23` and `swap13`, and the next stage reads that
layout. Each stage's field model, a block's two halves spliced in by `splice8`, is its layer with
the layouts applied (`leafStage8Field_eq` and its siblings); the layouts cancel between stages
(`perm16_perm16`), and passes of block-local maps compose block by block (`foldl_local16_comp`).
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Entries `i, …, i + 7` replaced by `v0, …, v7` where they exist: an eight-entry splice that keeps
the size. -/
def splice8 (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α) : Array α :=
  ((((((((a.setIfInBounds i v0).setIfInBounds (i + 1) v1).setIfInBounds (i + 2) v2).setIfInBounds
    (i + 3) v3).setIfInBounds (i + 4) v4).setIfInBounds (i + 5) v5).setIfInBounds (i + 6)
    v6).setIfInBounds (i + 7) v7)

@[simp] theorem size_splice8 (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α) :
    (splice8 a i v0 v1 v2 v3 v4 v5 v6 v7).size = a.size := by
  simp only [splice8, Array.size_setIfInBounds]

/-- Inside its range, an in-bounds `splice8` reads its values. -/
theorem getD_splice8_in (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α)
    (h : i + 8 ≤ a.size) (k : Nat) (d : α) (hk : i ≤ k ∧ k < i + 8) :
    (splice8 a i v0 v1 v2 v3 v4 v5 v6 v7).getD k d =
      #[v0, v1, v2, v3, v4, v5, v6, v7].getD (k - i) d := by
  obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i + o := ⟨k - i, by omega, by omega⟩
  unfold splice8
  interval_cases o <;>
    simp (disch := (first | omega | (simp only [Array.size_setIfInBounds]; omega))) only
      [getD_setIfInBounds, Nat.add_sub_cancel_left, Nat.add_zero, Nat.add_left_cancel_iff,
        Nat.reduceEqDiff, Nat.left_eq_add, Nat.succ_ne_zero, Nat.sub_self, ↓reduceIte,
        getD_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]

/-- Outside its range, `splice8` keeps the entries. -/
theorem getD_splice8_out (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α) (k : Nat) (d : α)
    (hk : k < i ∨ i + 8 ≤ k) :
    (splice8 a i v0 v1 v2 v3 v4 v5 v6 v7).getD k d = a.getD k d := by
  simp only [splice8, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  repeat rw [ite_eq_right (by omega)]

/-- An eight-entry literal has eight entries. -/
@[simp] theorem size_literal8 (v0 v1 v2 v3 v4 v5 v6 v7 : α) :
    (#[v0, v1, v2, v3, v4, v5, v6, v7]).size = 8 := rfl

/-- In bounds, `splice8` is the splice of its eight values. -/
theorem splice8_eq_splice (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α)
    (h : i + 8 ≤ a.size) :
    splice8 a i v0 v1 v2 v3 v4 v5 v6 v7 = splice a i #[v0, v1, v2, v3, v4, v5, v6, v7] := by
  apply array_eq_of_getD _ _ v0 (by rw [size_splice8, size_splice _ _ _ h])
  intro k
  rw [getD_splice _ _ _ h, size_literal8]
  by_cases hk : i ≤ k ∧ k < i + 8
  · rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ h _ _ hk, ite_eq_right (by omega),
      ite_eq_left hk.2]
  · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    split_ifs <;> first | rfl | omega

/-- The sixteen entries from `base` permuted by `σ`: entry `base + o` becomes entry
`base + σ o`, for `o < 16`, where the block lies in the array. -/
def perm16 [Zero α] (σ : Nat → Nat) (base : Nat) (a : Array α) : Array α :=
  let e (o : Nat) : α := a.getD (base + σ o) 0
  splice8 (splice8 a base (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7)) (base + 8)
    (e 8) (e 9) (e 10) (e 11) (e 12) (e 13) (e 14) (e 15)

@[simp] theorem size_perm16 [Zero α] (σ : Nat → Nat) (base : Nat) (a : Array α) :
    (perm16 σ base a).size = a.size := by
  simp only [perm16, size_splice8]

/-- Inside its block, `perm16` reads the permuted entry. -/
theorem getD_perm16_in [Zero α] (σ : Nat → Nat) (base : Nat) (a : Array α)
    (h : base + 16 ≤ a.size) (o : Nat) (ho : o < 16) :
    (perm16 σ base a).getD (base + o) 0 = a.getD (base + σ o) 0 := by
  unfold perm16
  dsimp only
  by_cases h8 : o < 8
  · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega),
      getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by omega) _ _ (by omega)]
    interval_cases o <;> simp only [Nat.add_sub_cancel_left, Nat.add_zero, Nat.sub_self] <;> rfl
  · rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ (by rw [size_splice8]; omega) _ _ (by omega)]
    interval_cases o <;> simp only [Nat.add_sub_add_left, Nat.reduceSub] <;> rfl

/-- The first entry of `perm16`'s block, after simplification has removed `+ 0`. -/
theorem getD_perm16_base [Zero α] (σ : Nat → Nat) (base : Nat) (a : Array α)
    (h : base + 16 ≤ a.size) : (perm16 σ base a).getD base 0 = a.getD (base + σ 0) 0 := by
  simpa only [Nat.add_zero] using getD_perm16_in σ base a h 0 (by decide)

/-- Outside its block, `perm16` keeps the entries. -/
theorem getD_perm16_out [Zero α] (σ : Nat → Nat) (base : Nat) (a : Array α) (k : Nat)
    (hk : k < base ∨ base + 16 ≤ k) : (perm16 σ base a).getD k 0 = a.getD k 0 := by
  unfold perm16
  dsimp only
  rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega),
    getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]

/-- A permutation of a block's sixteen entries that is its own inverse undoes itself. -/
theorem perm16_perm16 [Zero α] (σ : Nat → Nat) (hσ : ∀ o < 16, σ o < 16 ∧ σ (σ o) = o)
    (base : Nat) (a : Array α) (h : base + 16 ≤ a.size) :
    perm16 σ base (perm16 σ base a) = a := by
  apply array_eq_of_getD _ _ 0 (by rw [size_perm16, size_perm16])
  intro k
  by_cases hk : base ≤ k ∧ k < base + 16
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = base + o := ⟨k - base, by omega, by omega⟩
    rw [getD_perm16_in _ _ _ (by rw [size_perm16]; exact h) o ho,
      getD_perm16_in _ _ _ h _ (hσ o ho).1, (hσ o ho).2]
  · rw [getD_perm16_out _ _ _ _ (by omega), getD_perm16_out _ _ _ _ (by omega)]

/-- The layout of the second stage's output: block index bits `b₃ b₂ b₁ b₀` at position
`8 b₂ + 4 b₃ + 2 b₁ + b₀`, so that the sums and the products each fill eight consecutive words. -/
def swap23 (o : Nat) : Nat := #[0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15].getD o o

/-- The layout of the third stage's output: index bits `b₃ b₂ b₁ b₀` at position
`8 b₁ + 4 b₂ + 2 b₃ + b₀`. -/
def swap13 (o : Nat) : Nat := #[0, 1, 8, 9, 4, 5, 12, 13, 2, 3, 10, 11, 6, 7, 14, 15].getD o o

theorem swap23_invol (o : Nat) (ho : o < 16) : swap23 o < 16 ∧ swap23 (swap23 o) = o := by
  interval_cases o <;> decide

theorem swap13_invol (o : Nat) (ho : o < 16) : swap13 o < 16 ∧ swap13 (swap13 o) = o := by
  interval_cases o <;> decide


/-! ### Block-local passes -/

/-- `F` acts on the sixteen entries from `base` only: on arrays holding the block it keeps the
size and the other entries and computes the block's entries from the block. -/
structure Local16 [Zero α] (F : Array α → Array α) (base : Nat) : Prop where
  size : ∀ b, base + 16 ≤ b.size → (F b).size = b.size
  out : ∀ b, base + 16 ≤ b.size → ∀ k, (k < base ∨ base + 16 ≤ k) → (F b).getD k 0 = b.getD k 0
  dep : ∀ b b', base + 16 ≤ b.size → b'.size = b.size →
    (∀ o < 16, b'.getD (base + o) 0 = b.getD (base + o) 0) →
    ∀ o < 16, (F b').getD (base + o) 0 = (F b).getD (base + o) 0

theorem Local16.comp [Zero α] {F G : Array α → Array α} {base : Nat} (hF : Local16 F base)
    (hG : Local16 G base) : Local16 (fun b ↦ F (G b)) base where
  size b hb := by rw [hF.size _ (by rw [hG.size b hb]; exact hb), hG.size b hb]
  out b hb k hk := by
    rw [hF.out _ (by rw [hG.size b hb]; exact hb) k hk, hG.out b hb k hk]
  dep b b' hb hs he o ho :=
    hF.dep (G b) (G b') (by rw [hG.size b hb]; exact hb)
      (by rw [hG.size b' (by rw [hs]; exact hb), hG.size b hb, hs])
      (fun o' ho' ↦ hG.dep b b' hb hs he o' ho') o ho

theorem Local16.perm16 [Zero α] (σ : Nat → Nat) (hσ : ∀ o < 16, σ o < 16) (base : Nat) :
    Local16 (perm16 σ base : Array α → Array α) base where
  size b _ := size_perm16 σ base b
  out b _ k hk := getD_perm16_out σ base b k hk
  dep b b' hb hs he o ho := by
    rw [getD_perm16_in _ _ _ (by rw [hs]; exact hb) o ho, getD_perm16_in _ _ _ hb o ho,
      he _ (hσ o ho)]

/-- On blocks `0, …, n - 1` of `a`, passes of local maps leave each block computed from the
input's block, and the entries after them unchanged. -/
theorem getD_foldl_local16 [Zero α] (F : Nat → Array α → Array α)
    (hF : ∀ blk, Local16 (F blk) (blk * 16)) :
    ∀ (n : Nat) (a : Array α), 16 * n ≤ a.size →
      ((List.range n).foldl (fun b blk ↦ F blk b) a).size = a.size ∧
      ∀ k, ((List.range n).foldl (fun b blk ↦ F blk b) a).getD k 0 =
        if k < 16 * n then (F (k / 16) a).getD k 0 else a.getD k 0 := by
  intro n
  induction n with
  | zero =>
    intro a _
    exact ⟨rfl, fun k ↦ by rw [ite_eq_right (by omega)]; rfl⟩
  | succ n ih =>
    intro a ha
    obtain ⟨hsz, hget⟩ := ih a (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hb : n * 16 + 16 ≤ ((List.range n).foldl (fun b blk ↦ F blk b) a).size := by
      rw [hsz]; omega
    refine ⟨by rw [(hF n).size _ hb, hsz], fun k ↦ ?_⟩
    by_cases hk : n * 16 ≤ k ∧ k < n * 16 + 16
    · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = n * 16 + o := ⟨k - n * 16, by omega, by omega⟩
      rw [ite_eq_left (by omega), show (n * 16 + o) / 16 = n by omega]
      exact (hF n).dep a _ (by omega) hsz (fun o' ho' ↦ by rw [hget, ite_eq_right (by omega)]) o ho
    · rw [(hF n).out _ hb k (by omega), hget]
      by_cases hk' : k < 16 * n
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]

/-- Two passes of local maps over the same blocks are one pass of their composites. -/
theorem foldl_local16_comp [Zero α] (F G : Nat → Array α → Array α)
    (hF : ∀ blk, Local16 (F blk) (blk * 16)) (hG : ∀ blk, Local16 (G blk) (blk * 16))
    (n : Nat) (a : Array α) (ha : 16 * n ≤ a.size) :
    (List.range n).foldl (fun b blk ↦ G blk b) ((List.range n).foldl (fun b blk ↦ F blk b) a) =
      (List.range n).foldl (fun b blk ↦ G blk (F blk b)) a := by
  obtain ⟨hs1, hg1⟩ := getD_foldl_local16 F hF n a ha
  obtain ⟨hs2, hg2⟩ := getD_foldl_local16 G hG n _ (by rw [hs1]; exact ha)
  obtain ⟨hs3, hg3⟩ := getD_foldl_local16 (fun blk b ↦ G blk (F blk b))
    (fun blk ↦ (hG blk).comp (hF blk)) n a ha
  apply array_eq_of_getD _ _ 0 (by rw [hs2, hs1, hs3])
  intro k
  rw [hg2, hg3]
  by_cases hk : k < 16 * n
  · rw [ite_eq_left hk, ite_eq_left hk]
    obtain ⟨j, o, ho, rfl⟩ : ∃ j o, o < 16 ∧ k = j * 16 + o := ⟨k / 16, k % 16, by omega, by omega⟩
    have hj : (j * 16 + o) / 16 = j := by omega
    have hb : j * 16 + 16 ≤ a.size := by omega
    rw [hj]
    refine (hG j).dep _ _ (by rw [(hF _).size a hb]; exact hb)
      (by rw [hs1, (hF _).size a hb]) (fun o' ho' ↦ ?_) o ho
    rw [hg1, ite_eq_left (by omega), show (j * 16 + o') / 16 = j by omega]
  · rw [ite_eq_right hk, ite_eq_right hk, hg1, ite_eq_right hk]

/-- A layer's coordinate reads only its block's entries. -/
theorem layer16Value_congr [Field R] (tw a a' : Array R) (half base o : Nat)
    (hh : half = 8 ∨ half = 4 ∨ half = 2 ∨ half = 1) (ho : o < 16)
    (he : ∀ c < 16, a'.getD (base + c) 0 = a.getD (base + c) 0) :
    layer16Value tw half a' base o = layer16Value tw half a base o := by
  unfold layer16Value
  have h1 : o / (2 * half) * (2 * half) + o % half < 16 := by
    rcases hh with rfl | rfl | rfl | rfl <;> omega
  have h2 : o / (2 * half) * (2 * half) + o % half + half < 16 := by
    rcases hh with rfl | rfl | rfl | rfl <;> omega
  dsimp only
  rw [show base + o / (2 * half) * (2 * half) + o % half + half =
      base + (o / (2 * half) * (2 * half) + o % half + half) by omega,
    show base + o / (2 * half) * (2 * half) + o % half =
      base + (o / (2 * half) * (2 * half) + o % half) by omega, he _ h1, he _ h2]

theorem Local16.layer16_8 [Field R] (tw : Array R) (base : Nat) :
    Local16 (fun a : Array R ↦ layer16_8 tw a base) base where
  size b _ := size_layer16_8 tw b base
  out b hb k hk := getD_layer16_8_outside tw b base hb k (by omega)
  dep b b' hb hs he o ho := by
    rw [getD_layer16_8 tw b' base (by rw [hs]; exact hb) o ho, getD_layer16_8 tw b base hb o ho]
    exact layer16Value_congr tw b b' 8 base o (by decide) ho he

theorem Local16.layer16_4 [Field R] (tw : Array R) (base : Nat) :
    Local16 (fun a : Array R ↦ layer16_4 tw a base) base where
  size b _ := size_layer16_4 tw b base
  out b hb k hk := getD_layer16_4_outside tw b base hb k (by omega)
  dep b b' hb hs he o ho := by
    rw [getD_layer16_4 tw b' base (by rw [hs]; exact hb) o ho, getD_layer16_4 tw b base hb o ho]
    exact layer16Value_congr tw b b' 4 base o (by decide) ho he

theorem Local16.layer16_2 [Field R] (tw : Array R) (base : Nat) :
    Local16 (fun a : Array R ↦ layer16_2 tw a base) base where
  size b _ := size_layer16_2 tw b base
  out b hb k hk := getD_layer16_2_outside tw b base hb k (by omega)
  dep b b' hb hs he o ho := by
    rw [getD_layer16_2 tw b' base (by rw [hs]; exact hb) o ho, getD_layer16_2 tw b base hb o ho]
    exact layer16Value_congr tw b b' 2 base o (by decide) ho he

theorem Local16.layer16_1 [Field R] (tw : Array R) (base : Nat) :
    Local16 (fun a : Array R ↦ layer16_1 tw a base) base where
  size b _ := size_layer16_1 tw b base
  out b hb k hk := getD_layer16_1_outside tw b base hb k (by omega)
  dep b b' hb hs he o ho := by
    rw [getD_layer16_1 tw b' base (by rw [hs]; exact hb) o ho, getD_layer16_1 tw b base hb o ho]
    exact layer16Value_congr tw b b' 1 base o (by decide) ho he


namespace Expressions

/-- The first of the four final DIF layers on the sixteen-coordinate block at `base`, as the stage
kernel computes it. -/
def leafStage8Field [Zero R] [Add R] [Sub R] [Mul R] (t : Array R) (base : Nat) (b : Array R) :
    Array R :=
  leafStage8_fields%

/-- The second of the four final DIF layers on the block at `base`. -/
def leafStage4Field [Zero R] [Add R] [Sub R] [Mul R] (t : Array R) (base : Nat) (b : Array R) :
    Array R :=
  leafStage4_fields%

/-- The third of the four final DIF layers on the block at `base`. -/
def leafStage2Field [Zero R] [Add R] [Sub R] [Mul R] (t : Array R) (base : Nat) (b : Array R) :
    Array R :=
  leafStage2_fields%

/-- The last DIF layer on the block at `base`. -/
def leafStage1Field [Zero R] [Add R] [Sub R] (base : Nat) (b : Array R) : Array R :=
  leafStage1_fields%

@[simp] theorem size_leafStage8Field [Zero R] [Add R] [Sub R] [Mul R] (t b : Array R)
    (base : Nat) : (leafStage8Field t base b).size = b.size := by
  simp only [leafStage8Field, size_splice8]

set_option maxHeartbeats 1000000 in
/-- The first stage's model is the first of the four final layers. -/
theorem leafStage8Field_eq [Field R] (t b : Array R) (base : Nat) (hs : base + 16 ≤ b.size) :
    leafStage8Field t base b = layer16_8 t b base := by
  apply array_eq_of_getD _ _ (0 : R) (by rw [size_leafStage8Field, size_layer16_8])
  intro k
  by_cases hk : base ≤ k ∧ k < base + 16
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = base + o := ⟨k - base, by omega, by omega⟩
    rw [getD_layer16_8 t b base hs o ho]
    unfold leafStage8Field layer16Value
    interval_cases o <;>
      simp (disch := (first | omega | (simp only [size_splice8]; omega))) only [getD_splice8_in,
        getD_splice8_out, fieldAdd, fieldSub, fieldMul, getD_toArray, Nat.add_assoc,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT,
        Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.reduceSub, Nat.sub_self, Nat.add_zero,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ↓reduceIte]
  · rw [getD_layer16_8_outside t b base hs k hk]
    unfold leafStage8Field
    simp (disch := omega) only [getD_splice8_out]

@[simp] theorem size_leafStage4Field [Zero R] [Add R] [Sub R] [Mul R] (t b : Array R)
    (base : Nat) : (leafStage4Field t base b).size = b.size := by
  simp only [leafStage4Field, size_splice8]

set_option maxHeartbeats 1000000 in
/-- The second stage's model is the second of the four final layers, its block stored with the
sums in the first eight words and the products in the last eight (`swap23`). -/
theorem leafStage4Field_eq [Field R] (t b : Array R) (base : Nat) (hs : base + 16 ≤ b.size) :
    leafStage4Field t base b = perm16 swap23 base (layer16_4 t b base) := by
  apply array_eq_of_getD _ _ (0 : R) (by rw [size_leafStage4Field, size_perm16, size_layer16_4])
  intro k
  by_cases hk : base ≤ k ∧ k < base + 16
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = base + o := ⟨k - base, by omega, by omega⟩
    rw [getD_perm16_in _ _ _ (by rw [size_layer16_4]; exact hs) o ho,
      getD_layer16_4 t b base hs _ (swap23_invol o ho).1]
    unfold leafStage4Field layer16Value
    interval_cases o <;>
      simp (disch := (first | omega | (simp only [size_splice8]; omega))) only [getD_splice8_in,
        getD_splice8_out, fieldAdd, fieldSub, fieldMul, getD_toArray, swap23,
        Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT, Nat.add_sub_cancel_left, Nat.add_sub_add_left,
        Nat.reduceSub, Nat.sub_self, Nat.add_zero, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, ↓reduceIte]
  · rw [getD_perm16_out _ _ _ _ (by omega), getD_layer16_4_outside t b base hs k hk]
    unfold leafStage4Field
    simp (disch := omega) only [getD_splice8_out]

@[simp] theorem size_leafStage2Field [Zero R] [Add R] [Sub R] [Mul R] (t b : Array R)
    (base : Nat) : (leafStage2Field t base b).size = b.size := by
  simp only [leafStage2Field, size_splice8]

set_option maxHeartbeats 1000000 in
/-- The third stage's model is the third of the four final layers on a block stored as the second
stage stores it, its own block stored with the sums in the first eight words (`swap13`). -/
theorem leafStage2Field_eq [Field R] (t b : Array R) (base : Nat) (hs : base + 16 ≤ b.size) :
    leafStage2Field t base b =
      perm16 swap13 base (layer16_2 t (perm16 swap23 base b) base) := by
  have hs' : base + 16 ≤ (perm16 swap23 base b).size := by rw [size_perm16]; exact hs
  apply array_eq_of_getD _ _ (0 : R)
    (by rw [size_leafStage2Field, size_perm16, size_layer16_2, size_perm16])
  intro k
  by_cases hk : base ≤ k ∧ k < base + 16
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = base + o := ⟨k - base, by omega, by omega⟩
    rw [getD_perm16_in _ _ _ (by rw [size_layer16_2]; exact hs') o ho,
      getD_layer16_2 t _ base hs' _ (swap13_invol o ho).1]
    unfold leafStage2Field layer16Value
    interval_cases o <;>
      simp (disch := (first | omega | (simp only [size_splice8, size_perm16]; omega))) only
        [getD_splice8_in, getD_splice8_out, getD_perm16_in, getD_perm16_base,
        fieldAdd, fieldSub, fieldMul,
        getD_toArray, swap23, swap13, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT, Nat.add_sub_cancel_left, Nat.add_sub_add_left,
        Nat.reduceSub, Nat.sub_self, Nat.add_zero, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, ↓reduceIte]
  · rw [getD_perm16_out _ _ _ _ (by omega), getD_layer16_2_outside t _ base hs' k hk,
      getD_perm16_out _ _ _ _ (by omega)]
    unfold leafStage2Field
    simp (disch := omega) only [getD_splice8_out]

@[simp] theorem size_leafStage1Field [Zero R] [Add R] [Sub R] (b : Array R)
    (base : Nat) : (leafStage1Field base b).size = b.size := by
  simp only [leafStage1Field, size_splice8]

set_option maxHeartbeats 1000000 in
/-- The last stage's model is the last of the four final layers on a block stored as the third
stage stores it, its own block in natural order. -/
theorem leafStage1Field_eq [Field R] (b : Array R) (base : Nat) (hs : base + 16 ≤ b.size) :
    leafStage1Field base b = layer16_1 #[1] (perm16 swap13 base b) base := by
  have hs' : base + 16 ≤ (perm16 swap13 base b).size := by rw [size_perm16]; exact hs
  apply array_eq_of_getD _ _ (0 : R) (by rw [size_leafStage1Field, size_layer16_1, size_perm16])
  intro k
  by_cases hk : base ≤ k ∧ k < base + 16
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = base + o := ⟨k - base, by omega, by omega⟩
    rw [getD_layer16_1 #[1] _ base hs' o ho]
    unfold leafStage1Field layer16Value
    interval_cases o <;>
      simp (disch := (first | omega | (simp only [size_splice8]; omega))) only
        [one_mul, getD_splice8_in, getD_splice8_out, getD_perm16_in, getD_perm16_base,
        fieldAdd, fieldSub,
        getD_toArray, swap13, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT, Nat.add_sub_cancel_left, Nat.add_sub_add_left,
        Nat.reduceSub, Nat.sub_self, Nat.add_zero, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, ↓reduceIte]
  · rw [getD_layer16_1_outside #[1] _ base hs' k hk, getD_perm16_out _ _ _ _ (by omega)]
    unfold leafStage1Field
    simp (disch := omega) only [getD_splice8_out]

end Expressions

end CompPoly.CPolynomial.NTTFast.Packed
