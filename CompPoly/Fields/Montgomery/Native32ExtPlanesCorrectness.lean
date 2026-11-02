/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native32ExtPlanes
public import CompPoly.Fields.Montgomery.Native32WordsCorrectness
public import CompPoly.Fields.Montgomery.InterpolateCosetPackedCorrectness
public import Mathlib.FieldTheory.Finite.Trace

/-!
# Correctness of the coordinate planes

Planes represent the elements whose coordinates they encode (`ExtPlanes.Rel`). Every plane
operation represents the extension's operation on the represented arrays: sums, differences,
products by base vectors and extension scalars, elementwise products (`mul_rel`), batch inverses
with zero to zero (`batchInv_rel`), concatenation of parallel pieces (`join_rel`), and the
inverses of `z - x` for `z` outside the base field (`invDenoms_rel`).

The products are the spec's product formula with the reduction split off (`coord_mul_reduce`),
and `invDenoms_rel` rests on the norm: `∏_{j < d} φʲ(y)` lies in the base field for the Frobenius
`φ : y ↦ y^p` (`FiniteField.algebraMap_norm_eq_prod_pow`).
-/

@[expose] public section

namespace Montgomery.Native32

open CompPoly CompPoly.Extension
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields getD_ofFn_bounded ofWord_val)
open CompPoly.CPolynomial.NTTFast.Packed.Native (zeroWords read)
open Words

/-! ### Fast extensions -/

namespace FastExt

variable {p : ℕ} [Mont32Field p] {E : Type} [FastExt p E]

local notation "F" => FastField p
local notation "d" => FastExt.d p E

@[simp] theorem toSpec_pow (a : E) (n : ℕ) : toSpec (pow a n) = toSpec a ^ n := by
  let : Semigroup E := { mul_assoc := mul_assoc }
  induction n with
  | zero => rw [pow, npowBinRec_zero, toSpec_one, _root_.pow_zero]
  | succ n ih => rw [pow, npowBinRec_succ, ← pow, toSpec_mul, ih, _root_.pow_succ]

theorem coord_eq_zero_iff {a : E} : a = 0 ↔ toSpec a = 0 :=
  ⟨fun h ↦ h ▸ toSpec_zero, fun h ↦ toSpec_injective (h.trans toSpec_zero.symm)⟩

theorem coord_smul_ofBase (x : F) (a : E) (k : Fin d) :
    coord (ofBase x * a) k = x * coord a k := by
  rw [← coeff_toSpec, toSpec_mul, toSpec_ofBase, ← Ext.algebraMap_eq_ofBase, ← Algebra.smul_def,
    Ext.coeff_smul, coeff_toSpec]

theorem coord_mul_ofBase (a : E) (x : F) (k : Fin d) :
    coord (a * ofBase x) k = coord a k * x := by
  rw [mul_comm, coord_smul_ofBase, _root_.mul_comm]

theorem coord_ofBase (x : F) (k : Fin d) :
    coord (ofBase (E := E) x) k = if (k : ℕ) = 0 then x else 0 := by
  rw [← coeff_toSpec, toSpec_ofBase, Ext.coeff_ofBase]

/-- A coordinate of the spec field, as an additive map. -/
def coeffHom (m : Fin d) : Spec p E →+ F where
  toFun x := Ext.coeff x m
  map_zero' := Ext.coeff_zero m
  map_add' x y := Ext.coeff_add x y m

theorem coeff_sum {ι : Type} (s : Finset ι) (g : ι → Spec p E) (m : Fin d) :
    Ext.coeff (∑ i ∈ s, g i) m = ∑ i ∈ s, Ext.coeff (g i) m :=
  map_sum (coeffHom (E := E) m) g s

/-- The basis expansion of a spec element. -/
theorem ofFn_eq_sum (g : Fin d → F) :
    (Ext.ofFn g : Spec p E) = ∑ i : Fin d, g i • (Ext.gen : Spec p E) ^ (i : ℕ) := by
  ext m
  rw [Ext.coeff_ofFn, coeff_sum]
  simp only [Ext.coeff_smul, Ext.gen_pow_of_lt (Fin.isLt _), Ext.coeff_ofFn, mul_ite, mul_one,
    mul_zero]
  simp only [Fin.val_inj]
  rw [Finset.sum_ite_eq Finset.univ m]
  simp only [Finset.mem_univ, ite_true]

/-- Coordinate `m` of a product: `∑ᵢ aᵢ [Xⁱ s]ₘ`. -/
theorem coord_mul_eq_sum (a s : E) (m : Fin d) :
    coord (a * s) m = ∑ i : Fin d, coord a i * coord (pow gen i * s) m := by
  have h : toSpec (a * s) = ∑ i : Fin d, coord a i • toSpec (pow gen i * s) := by
    rw [toSpec_mul, toSpec, ofFn_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [toSpec_mul, toSpec_pow, toSpec_gen, smul_mul_assoc]
  rw [← coeff_toSpec, h, coeff_sum]
  simp only [Ext.coeff_smul, coeff_toSpec]

/-- Coordinate `k` of the unreduced product of the coordinates `x` and `y`. -/
def conv (x y : Fin d → F) (k : ℕ) : F :=
  ∑ i : Fin d, if h : (i : ℕ) ≤ k ∧ k - (i : ℕ) < d then x i * y ⟨k - (i : ℕ), h.2⟩ else 0

/-- **Coordinates of products**, reduced as the planes reduce them: coordinate `m` of the
unreduced product plus the coordinates `k ≥ d` times `[Xᵏ mod f]ₘ`. -/
theorem coord_mul_reduce (a b : E) (m : Fin d) :
    coord (a * b) m = conv (coord a) (coord b) m +
      ((List.range' d (d - 1)).map fun k ↦
        conv (coord a) (coord b) k * Ext.coeff (Ext.monomialMod k : Spec p E) m).sum := by
  rw [← coeff_toSpec, toSpec_mul, Ext.coeff_mul_reduce]
  simp only [Ext.conv, conv, coeff_toSpec]

end FastExt

namespace ExtPlanes

variable {p : ℕ} [Mont32Field p] {E : Type} [FastExt p E]

local notation "F" => FastField p
local notation "d" => FastExt.d p E

/-! ### Representation -/

@[simp] theorem getElem_ofFn_fin {α : Type} {n : Nat} (g : Fin n → α) (k : Fin n) :
    (Vector.ofFn g)[k] = g k := by
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

@[simp] theorem getElem_replicate_fin {α : Type} {n : Nat} (x : α) (k : Fin n) :
    (Vector.replicate n x)[k] = x := by
  simp only [Fin.getElem_fin, Vector.getElem_replicate]

/-- An in-range coordinate of an array of extension elements. -/
theorem getD_map {α : Type} (a : Array α) (pr : α → F) (i : Nat) (h : i < a.size) :
    (a.map pr).getD i 0 = pr a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem h]
  rfl

/-- Planes represent tabulated elements when they tabulate the coordinates. -/
theorem rel_tab_iff {B : Nat} {v : ExtPlanes p E} {f : Nat → E} :
    Rel v (tab B f) ↔
      v.n = B ∧ ∀ k : Fin d, v.c[k] = encode (tab B fun i ↦ FastExt.coord (f i) k) := by
  simp only [Rel, size_tab, tab_map]

theorem Rel.congr_tab {B : Nat} {v : ExtPlanes p E} {f g : Nat → E} (h : Rel v (tab B f))
    (hfg : ∀ i < B, f i = g i) : Rel v (tab B g) := by
  rw [← tab_congr hfg]; exact h

theorem Rel.congr {v : ExtPlanes p E} {a b : Array E} (h : Rel v a) (e : a = b) : Rel v b :=
  e ▸ h

/-- An array is its tabulated elements. -/
theorem tab_getD (a : Array E) : a = tab a.size fun i ↦ a.getD i 0 := by
  apply Array.ext (by rw [size_tab])
  intro i hi _
  rw [getElem_tab, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]

/-- Planes of tabulated coordinates represent the elements with those coordinates. -/
theorem rel_mk {B : Nat} (c : Vector ByteArray d) (f : Nat → E)
    (h : ∀ k : Fin d, c[k] = encode (tab B fun i ↦ FastExt.coord (f i) k)) :
    Rel ⟨B, c⟩ (tab B f) :=
  rel_tab_iff.mpr ⟨rfl, h⟩

/-- Represented, indexable planes read back their elements. -/
theorem get_eq {B : Nat} {v : ExtPlanes p E} {f : Nat → E} (hv : Rel v (tab B f))
    (hB : 4 * B < USize.size) (i : Nat) (hi : i < B) : v.get i = f i := by
  obtain ⟨-, hc⟩ := rel_tab_iff.mp hv
  refine FastExt.ext fun k ↦ ?_
  simp only [get, FastExt.coord_ofCoords]
  rw [hc k, read_tab hB _ _ hi, ofWord_val]

/-- Represented, indexable planes read back their elements. -/
theorem toArray_eq {v : ExtPlanes p E} {a : Array E} (hv : Rel v a)
    (hs : 4 * a.size < USize.size) : v.toArray = a := by
  rw [tab_getD a] at hv ⊢
  have hn := (rel_tab_iff.mp hv).1
  apply Array.ext (by simp only [toArray, Array.size_ofFn, size_tab, hn])
  intro i hi _
  simp only [toArray, Array.size_ofFn, hn] at hi
  simp only [toArray, Array.getElem_ofFn, getElem_tab, get_eq hv hs i hi]

/-- The planes of an array represent it. -/
theorem ofArray_rel (a : Array E) : Rel (ofArray a) a :=
  ⟨rfl, fun k ↦ by
    simp only [ofArray, getElem_ofFn_fin]
    exact CompPoly.CPolynomial.NTTFast.Packed.Native.encodeFields_eq _⟩

/-- Zero planes represent zeros. -/
theorem zeros_rel (n : Nat) : Rel (zeros (E := E) n) (Array.replicate n 0) := by
  refine ⟨(Array.size_replicate ..).symm, fun k ↦ ?_⟩
  simp only [zeros, getElem_replicate_fin, zeroWords_eq (p := p), Array.map_replicate,
    FastExt.coord_zero, Pi.zero_apply]

/-! ### Linear operations -/

/-- Elementwise sums. -/
theorem add_rel {B : Nat} (hB : 4 * B < USize.size) {v w : ExtPlanes p E} {f g : Nat → E}
    (hv : Rel v (tab B f)) (hw : Rel w (tab B g)) :
    Rel (v.add w) (tab B fun i ↦ f i + g i) := by
  obtain ⟨hvn, hvc⟩ := rel_tab_iff.mp hv
  obtain ⟨-, hwc⟩ := rel_tab_iff.mp hw
  simp only [add, hvn]
  refine rel_mk _ _ fun k ↦ ?_
  rw [getElem_ofFn_fin, hvc, hwc, addWords_tab hB]
  simp only [FastExt.coord_add, Pi.add_apply]

/-- Elementwise differences. -/
theorem sub_rel {B : Nat} (hB : 4 * B < USize.size) {v w : ExtPlanes p E} {f g : Nat → E}
    (hv : Rel v (tab B f)) (hw : Rel w (tab B g)) :
    Rel (v.sub w) (tab B fun i ↦ f i - g i) := by
  obtain ⟨hvn, hvc⟩ := rel_tab_iff.mp hv
  obtain ⟨-, hwc⟩ := rel_tab_iff.mp hw
  simp only [sub, hvn]
  refine rel_mk _ _ fun k ↦ ?_
  rw [getElem_ofFn_fin, hvc, hwc, subWords_tab hB]
  simp only [FastExt.coord_sub, Pi.sub_apply]

/-- A scalar minus every element. -/
theorem rsub_rel {B : Nat} (hB : 4 * B < USize.size) (s : E) {v : ExtPlanes p E} {f : Nat → E}
    (hv : Rel v (tab B f)) : Rel (rsub s v) (tab B fun i ↦ s - f i) := by
  obtain ⟨hvn, hvc⟩ := rel_tab_iff.mp hv
  simp only [rsub, hvn]
  refine rel_mk _ _ fun k ↦ ?_
  rw [getElem_ofFn_fin, hvc, replicateWord_tab hB,
    subWords_tab hB]
  simp only [FastExt.coord_sub, Pi.sub_apply]

/-- Every element times a base element. -/
theorem mulBase_rel {B : Nat} (hB : 4 * B < USize.size) {v : ExtPlanes p E} {f : Nat → E}
    (g : Nat → F) (hv : Rel v (tab B f)) :
    Rel (v.mulBase (encode (tab B g))) (tab B fun i ↦ f i * FastExt.ofBase (g i)) := by
  obtain ⟨hvn, hvc⟩ := rel_tab_iff.mp hv
  simp only [mulBase, hvn]
  refine rel_mk _ _ fun k ↦ ?_
  rw [getElem_ofFn_fin, hvc, mulWords_tab hB]
  simp only [FastExt.coord_mul_ofBase]

/-- Planes of parallel pieces, concatenated. -/
theorem join_rel (n parts : Nat) (V : Nat → ExtPlanes p E) (A : Nat → Array E)
    (hV : ∀ k < parts, Rel (V k) (A k))
    (hn : n = ((List.range parts).foldl (fun acc k ↦ acc ++ A k) #[]).size) :
    Rel (join n ((Array.range parts).map fun k ↦ Task.spawn fun _ ↦ (V k).c.toArray))
      ((List.range parts).foldl (fun acc k ↦ acc ++ A k) #[]) := by
  refine ⟨hn, fun k ↦ ?_⟩
  simp only [join, getElem_ofFn_fin, ← Array.foldl_toList, Array.toList_map, List.foldl_map,
    Array.toList_range, get_spawn]
  have hk : ∀ j < parts, (V j).c.toArray.getD k .empty = encode ((A j).map (FastExt.coord · k)) :=
    fun j hj ↦ by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp), Option.getD_some]
      exact (hV j hj).2 k
  rw [show ByteArray.emptyWithCapacity (4 * n) = ByteArray.empty from rfl]
  refine (foldl_bytes parts _ (fun j ↦ (A j).map (FastExt.coord · k)) hk).trans ?_
  rw [← foldl_append_map, Array.map_empty]


/-! ### Products -/

/-- Multiply-adds of tabulated planes by the nonzero scalars. -/
theorem combine_tab {B : Nat} (hB : 4 * B < USize.size) (k : Nat) (P : Nat → ByteArray)
    (f : Nat → Nat → F) (s : Nat → F) (hP : ∀ i, P i = encode (tab B (f i)))
    (hs : ∀ i, k ≤ i → s i = 0) :
    combine p B k P s = encode (tab B fun x ↦ ∑ i ∈ Finset.range k, f i x * s i) := by
  unfold combine
  -- After `G` groups, the sum of the first `4 G` terms.
  have key : ∀ G, (List.range G).foldl (fun acc g ↦
      mulAdd4Into p acc (P (4 * g)) (P (4 * g + 1)) (P (4 * g + 2)) (P (4 * g + 3)) 0 0 0 0
        (s (4 * g)).val (s (4 * g + 1)).val (s (4 * g + 2)).val (s (4 * g + 3)).val B)
      (zeroWords B) = encode (tab B fun x ↦ ∑ i ∈ Finset.range (4 * G), f i x * s i) := by
    intro G
    induction G with
    | zero =>
      rw [List.range_zero, List.foldl_nil, zeroWords_tab (p := p)]
      simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty]
    | succ G ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, hP, hP, hP, hP]
      have e := mulAdd4Into_encode (p := p) (tab B fun x ↦ ∑ i ∈ Finset.range (4 * G), f i x * s i)
        (tab B (f (4 * G))) (tab B (f (4 * G + 1))) (tab B (f (4 * G + 2)))
        (tab B (f (4 * G + 3))) 0 0 0 0 (s (4 * G)) (s (4 * G + 1)) (s (4 * G + 2))
        (s (4 * G + 3)) (by rw [size_tab, size_tab]; omega) (by rw [size_tab, size_tab]; omega)
        (by rw [size_tab, size_tab]; omega) (by rw [size_tab, size_tab]; omega)
        (by rw [size_tab]; exact hB) (by rw [size_tab]; exact hB) (by rw [size_tab]; exact hB)
        (by rw [size_tab]; exact hB) (by rw [size_tab]; exact hB)
      rw [size_tab] at e
      rw [e]
      refine congrArg encode (Array.ext (by simp only [Array.size_ofFn, size_tab])
        fun x hx _ ↦ ?_)
      simp only [Array.size_ofFn] at hx
      rw [Array.getElem_ofFn, getElem_tab]
      rw [getD_tab _ _ _ hx, Nat.zero_add, getD_tab _ _ _ hx, getD_tab _ _ _ hx,
        getD_tab _ _ _ hx, getD_tab _ _ _ hx, show 4 * (G + 1) = 4 * G + 1 + 1 + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      ring
  rw [key]
  refine congrArg encode (tab_congr fun x _ ↦ ?_)
  rw [show 4 * ((k + 3) / 4) = k + (4 * ((k + 3) / 4) - k) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (4 * ((k + 3) / 4) - k))
    fun i _ ↦ by rw [hs _ (Nat.le_add_right _ _), mul_zero], add_zero]

/-- Sums of tabulated planes. -/
theorem sumWords_map {B : Nat} (hB : 4 * B < USize.size) (L : List (Nat → F)) :
    sumWords p B (L.map fun g ↦ encode (tab B g)) = encode (tab B fun x ↦ (L.map (· x)).sum) := by
  cases L with
  | nil => simp only [List.map_nil, sumWords, zeroWords_tab (p := p), List.sum_nil]
  | cons g L =>
    simp only [List.map_cons, sumWords, List.sum_cons]
    suffices ∀ g, (L.map fun g ↦ encode (tab B g)).foldl (fun acc y ↦ addWords p acc y B)
        (encode (tab B g)) = encode (tab B fun x ↦ g x + (L.map (· x)).sum) from this g
    intro g
    induction L generalizing g with
    | nil => simp only [List.map_nil, List.foldl_nil, List.sum_nil, add_zero]
    | cons h L ih =>
      rw [List.map_cons, List.foldl_cons, addWords_tab hB, ih]
      simp only [List.map_cons, List.sum_cons, add_assoc]

/-- `acc + x · s` on tabulated planes. -/
theorem addScaled_tab {B : Nat} (hB : 4 * B < USize.size) (f g : Nat → F) (s : F) :
    addScaled p B (encode (tab B f)) (encode (tab B g)) s =
      encode (tab B fun x ↦ f x + g x * s) := by
  unfold addScaled
  split_ifs with h1 h2
  · rw [addWords_tab hB, h1]; simp only [mul_one]
  · rw [subWords_tab hB, h2]; simp only [mul_neg, mul_one, sub_eq_add_neg]
  · rw [mulAddWords_tab hB]

/-- The reduction of tabulated planes. -/
theorem reduceCoord_tab {B : Nat} (hB : 4 * B < USize.size) (tbl : Array (FastExt.Spec p E))
    (P : Nat → ByteArray) (C : Nat → Nat → F) (m : Fin d)
    (hP : ∀ k : Nat, (k = (m : ℕ) ∨ k ∈ List.range' d (d - 1)) → P k = encode (tab B (C k))) :
    reduceCoord tbl P B m = encode (tab B fun x ↦ C m x +
      ((List.range' d (d - 1)).map fun k ↦ C k x * Ext.coeff (tbl.getD k 0) m).sum) := by
  unfold reduceCoord
  rw [hP m (Or.inl rfl)]
  have hl : ∀ k ∈ List.range' d (d - 1), P k = encode (tab B (C k)) := fun k hk ↦ hP k (Or.inr hk)
  generalize C m = g
  generalize List.range' d (d - 1) = l at hl ⊢
  induction l generalizing g with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons k l ih =>
    have hl' : ∀ j ∈ l, P j = encode (tab B (C j)) := fun j hj ↦ hl j (List.mem_cons_of_mem _ hj)
    rw [List.foldl_cons]
    dsimp only
    split_ifs with hs
    · rw [ih _ hl']
      simp only [List.map_cons, List.sum_cons, hs, mul_zero, zero_add]
    · rw [hl k List.mem_cons_self, addScaled_tab hB, ih _ hl']
      simp only [List.map_cons, List.sum_cons, add_assoc]

/-- Sums of the planes kept by a condition. -/
theorem sumWords_filterMap {B : Nat} (hB : 4 * B < USize.size) {ι : Type} (l : List ι)
    (c : ι → Prop) [DecidablePred c] (P : (i : ι) → c i → ByteArray) (f : ι → Nat → F)
    (hP : ∀ i h, P i h = encode (tab B (f i))) :
    sumWords p B (l.filterMap fun i ↦ if h : c i then some (P i h) else none) =
      encode (tab B fun x ↦ (l.map fun i ↦ if c i then f i x else 0).sum) := by
  have e : (l.filterMap fun i ↦ if h : c i then some (P i h) else none) =
      ((l.filter fun i ↦ decide (c i)).map f).map fun g ↦ encode (tab B g) := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      by_cases h : c i
      · rw [List.filterMap_cons, dite_eq_left h, ih, hP]
        simp only [List.filter_cons, decide_eq_true h, ite_true, List.map_cons]
      · rw [List.filterMap_cons, dite_eq_right h, ih]
        simp only [List.filter_cons, decide_eq_false h, Bool.false_eq_true, ite_false]
  rw [e, sumWords_map hB]
  clear e
  congr 2
  funext x
  rw [List.map_map]
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases h : c i
    · simp only [List.filter_cons, decide_eq_true h, ite_true, List.map_cons, List.sum_cons,
        Function.comp_apply, ih, ite_eq_left h]
    · simp only [List.filter_cons, decide_eq_false h, Bool.false_eq_true, ite_false, ih,
        List.map_cons, List.sum_cons, ite_eq_right h, zero_add]

theorem sum_finRange {M : Type} [AddCommMonoid M] (g : Fin d → M) :
    ((List.finRange d).map g).sum = ∑ i : Fin d, g i := by
  rw [Fin.sum_univ_def]

/-- Planes of the unreduced product. -/
theorem convPlane_tab {B : Nat} (hB : 4 * B < USize.size) {v w : ExtPlanes p E} {f g : Nat → E}
    (hv : Rel v (tab B f)) (hw : Rel w (tab B g)) (k : Nat) :
    convPlane v w k = encode (tab B fun x ↦ FastExt.conv (FastExt.coord (f x))
      (FastExt.coord (g x)) k) := by
  obtain ⟨hvn, hvc⟩ := rel_tab_iff.mp hv
  obtain ⟨-, hwc⟩ := rel_tab_iff.mp hw
  unfold convPlane
  rw [hvn, sumWords_filterMap hB (List.finRange d) _ _
    (fun (i : Fin d) x ↦ if h : (i : ℕ) ≤ k ∧ k - (i : ℕ) < d then
      FastExt.coord (f x) i * FastExt.coord (g x) ⟨k - (i : ℕ), h.2⟩ else 0)]
  · refine congrArg encode (tab_congr fun x _ ↦ ?_)
    rw [sum_finRange, FastExt.conv]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> rfl
  · intro i h
    rw [show v.c[i] = v.c[i] from rfl, hvc i,
      show w.c[k - (i : ℕ)]'h.2 = w.c[(⟨k - (i : ℕ), h.2⟩ : Fin d)] from rfl, hwc,
      mulWords_tab hB]
    exact congrArg encode (tab_congr fun x _ ↦ by rw [dite_eq_left h])

/-- Elementwise products. -/
theorem mul_rel {B : Nat} (hB : 4 * B < USize.size) {v w : ExtPlanes p E} {f g : Nat → E}
    (hv : Rel v (tab B f)) (hw : Rel w (tab B g)) :
    Rel (v.mul w) (tab B fun i ↦ f i * g i) := by
  have hvn := (rel_tab_iff.mp hv).1
  have hd : 2 * d - 1 = d + (d - 1) := by
    have := (FastExt.params (p := p) (E := E)).d_pos; omega
  simp only [mul, hvn]
  refine rel_mk _ _ fun m ↦ ?_
  rw [getElem_ofFn_fin, reduceCoord_tab hB _ _
    (fun k x ↦ FastExt.conv (FastExt.coord (f x)) (FastExt.coord (g x)) k) m]
  · refine congrArg encode (tab_congr fun x _ ↦ ?_)
    rw [FastExt.coord_mul_reduce]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun k hk ↦ ?_)
    rw [List.mem_range'_1] at hk
    simp only [FastExt.d] at hk hd
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp; omega),
      Option.getD_some, Vector.getElem_toArray, Ext.red_getElem]
  · intro k hk
    have hk' : k < 2 * d - 1 := by
      rcases hk with rfl | hk
      · omega
      · rw [List.mem_range'_1] at hk; simp only [FastExt.d] at hk hd ⊢; omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp; omega), Option.getD_some,
      Array.getElem_ofFn, convPlane_tab hB hv hw]

/-- Every element times an extension scalar. -/
theorem smul_rel {B : Nat} (hB : 4 * B < USize.size) {v : ExtPlanes p E} {f : Nat → E} (s : E)
    (hv : Rel v (tab B f)) : Rel (v.smul s) (tab B fun i ↦ f i * s) := by
  obtain ⟨hvn, hvc⟩ := rel_tab_iff.mp hv
  simp only [smul, hvn]
  refine rel_mk _ _ fun m ↦ ?_
  rw [getElem_ofFn_fin]
  have hd := (FastExt.params (p := p) (E := E)).d_pos
  rw [combine_tab hB d _
    (fun i x ↦ if h : i < d then FastExt.coord (f x) ⟨i, h⟩ else FastExt.coord (f x) ⟨0, hd⟩) _
    (fun i ↦ by
      by_cases h : i < d
      · simp only [h, dite_true]; exact hvc ⟨i, h⟩
      · simp only [h, dite_false]; exact hvc ⟨0, hd⟩)
    (fun i hi ↦ by simp only [show ¬i < d by omega, dite_false])]
  refine congrArg encode (tab_congr fun x _ ↦ ?_)
  rw [FastExt.coord_mul_eq_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [i.isLt, dite_true, Fin.eta, Vector.getElem_ofFn]

/-- Inverses, zero to zero, by batch inversion of the elements. -/
theorem batchInv_rel {v : ExtPlanes p E} {a : Array E} (hv : Rel v a)
    (hs : 4 * a.size < USize.size) : Rel v.batchInv (a.map (·⁻¹)) := by
  unfold batchInv
  rw [toArray_eq hv hs]
  refine (ofArray_rel _).congr ?_
  rw [CompPoly.Array.batchInv_eq FastExt.toSpec FastExt.toSpec_injective FastExt.toSpec_mul
    FastExt.toSpec_inv FastExt.toSpec_one _ fun x hx ↦ ?_]
  · apply Array.ext (by simp)
    intro i h1 h2
    simp only [Array.getElem_zipWith, Array.getElem_map]
    split_ifs with h
    · rw [h]
      exact FastExt.toSpec_injective (by rw [FastExt.toSpec_zero, FastExt.toSpec_inv,
        FastExt.toSpec_zero, inv_zero])
    · rfl
  · obtain ⟨y, -, rfl⟩ := Array.mem_map.mp hx
    split_ifs with h
    · rw [FastExt.toSpec_one]; exact one_ne_zero
    · exact fun h' ↦ h (FastExt.toSpec_injective (h'.trans FastExt.toSpec_zero.symm))


/-! ### Inverses of `z - x` -/

section InvDenoms

open Polynomial in
/-- The spec field has degree `d` over the base field. -/
theorem finrank_spec : Module.finrank F (FastExt.Spec p E) = d := by
  have hc := Module.card_eq_pow_finrank (K := F) (V := FastExt.Spec p E)
  rw [Ext.card_ext, ← FastExt.card.out, card_fastField, natCard_fastField] at hc
  exact (Nat.pow_right_injective (Mont32Field.prime (modulus := p)).two_le hc).symm

/-- `(y - x)^(p^j) = y^(p^j) - x` for a base element `x`. -/
theorem sub_ofBase_pow (y : FastExt.Spec p E) (x : F) (j : ℕ) :
    (y - Ext.ofBase x) ^ (p ^ j) = y ^ (p ^ j) - Ext.ofBase x := by
  induction j with
  | zero => rw [pow_zero, pow_one, pow_one]
  | succ j ih =>
    have h := map_sub (FiniteField.frobeniusAlgHom F (FastExt.Spec p E)) (y ^ (p ^ j))
      (algebraMap F _ x)
    rw [AlgHom.commutes, FiniteField.frobeniusAlgHom_apply, FiniteField.frobeniusAlgHom_apply,
      card_fastField] at h
    rw [pow_succ, pow_mul, ih, ← Ext.algebraMap_eq_ofBase, h, ← pow_mul]

/-- **The norm lies in the base field**: `∏_{j < d} y^(p^j)`. -/
theorem prod_frob_mem (y : FastExt.Spec p E) :
    ∏ j ∈ Finset.range d, y ^ (p ^ j) = Ext.ofBase (Algebra.norm F y) := by
  have h := FiniteField.algebraMap_norm_eq_prod_pow F (FastExt.Spec p E) y
  rw [finrank_spec, natCard_fastField] at h
  rw [← h, Ext.algebraMap_eq_ofBase]

/-- `∑ₖ csₖ yᵏ` in the spec field. -/
def evalSpec (cs : List E) (y : FastExt.Spec p E) : FastExt.Spec p E :=
  ((List.range cs.length).map fun k ↦ FastExt.toSpec (cs.getD k 0) * y ^ k).sum

theorem sum_range_list {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem length_mulLinear (cs : List E) (w : E) : (mulLinear cs w).length = cs.length + 1 := by
  simp only [mulLinear, List.length_map, List.length_range]

theorem evalSpec_mulLinear (cs : List E) (w : E) (y : FastExt.Spec p E) :
    evalSpec (mulLinear cs w) y = (FastExt.toSpec w - y) * evalSpec cs y := by
  have hget : ∀ k, (mulLinear cs w).getD k 0 =
      if k < cs.length + 1 then w * cs.getD k 0 - (if k = 0 then 0 else cs.getD (k - 1) 0)
      else 0 := fun k ↦ by
    unfold mulLinear
    by_cases hk : k < cs.length + 1
    · rw [ite_eq_left hk, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some]
    · rw [ite_eq_right hk,
        List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega)]
  unfold evalSpec
  rw [length_mulLinear, sum_range_list, sum_range_list]
  have hlast : FastExt.toSpec (cs.getD cs.length 0) = 0 := by
    rw [List.getD_eq_default _ _ (le_refl _), FastExt.toSpec_zero]
  have e1 : ∀ k ∈ Finset.range (cs.length + 1),
      FastExt.toSpec ((mulLinear cs w).getD k 0) * y ^ k =
        FastExt.toSpec w * FastExt.toSpec (cs.getD k 0) * y ^ k -
          (if k = 0 then 0 else FastExt.toSpec (cs.getD (k - 1) 0) * y ^ k) := by
    intro k hk
    rw [hget, ite_eq_left (Finset.mem_range.mp hk)]
    by_cases h0 : k = 0
    · rw [ite_eq_left h0, ite_eq_left h0, FastExt.toSpec_sub, FastExt.toSpec_zero, sub_zero,
        sub_zero,
        FastExt.toSpec_mul]
    · rw [ite_eq_right h0, ite_eq_right h0, FastExt.toSpec_sub, FastExt.toSpec_mul, sub_mul]
  rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, Finset.sum_range_succ, hlast,
    Finset.sum_range_succ']
  simp only [mul_zero, zero_mul, add_zero, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
    ite_true]
  rw [sub_mul, Finset.mul_sum, Finset.mul_sum]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun k _ ↦ ?_) (Finset.sum_congr rfl fun k _ ↦ ?_)
  · rw [mul_assoc]
  · rw [pow_succ, mul_comm y, mul_assoc]

theorem prod_range_list {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih, List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem evalSpec_adj_aux (z : E) (l : List ℕ) (cs : List E) (y : FastExt.Spec p E) :
    evalSpec (l.foldl (fun cs j ↦ mulLinear cs (FastExt.frobE (j + 1) z)) cs) y =
      evalSpec cs y * (l.map fun j ↦ FastExt.toSpec z ^ (p ^ (j + 1)) - y).prod ∧
    (l.foldl (fun cs j ↦ mulLinear cs (FastExt.frobE (j + 1) z)) cs).length =
      cs.length + l.length := by
  induction l generalizing cs with
  | nil => simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one, List.length_nil,
      add_zero, and_self]
  | cons j l ih =>
    rw [List.foldl_cons, (ih _).1, (ih _).2, evalSpec_mulLinear, length_mulLinear]
    refine ⟨?_, by simp only [List.length_cons]; omega⟩
    rw [List.map_cons, List.prod_cons, FastExt.frobE, FastExt.toSpec_pow]
    ring

/-- The other conjugates: `adj(y) = ∏_{1 ≤ j < d} (z^(p^j) - y)`. -/
theorem evalSpec_adj (z : E) (y : FastExt.Spec p E) :
    evalSpec (adjCoeffs z) y =
      ∏ j ∈ Finset.range (d - 1), (FastExt.toSpec z ^ (p ^ (j + 1)) - y) ∧
    (adjCoeffs z).length = d := by
  obtain ⟨h1, h2⟩ := evalSpec_adj_aux z (List.range (d - 1)) [1] y
  refine ⟨?_, ?_⟩
  · rw [adjCoeffs, h1, prod_range_list]
    have h1 : evalSpec [(1 : E)] y = 1 := by
      simp only [evalSpec, List.length_singleton, List.range_one, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, pow_zero, mul_one]
      exact FastExt.toSpec_one
    rw [h1, one_mul]
  · rw [adjCoeffs, h2, List.length_range, List.length_singleton]
    have := (FastExt.params (p := p) (E := E)).d_pos
    simp only [FastExt.d] at this ⊢
    omega

/-- The coordinates of `∑ₖ csₖ xᵏ` at a base point. -/
theorem coeff_evalSpec (cs : List E) (x : F) (m : Fin d) :
    Ext.coeff (evalSpec cs (Ext.ofBase x)) m =
      ∑ k ∈ Finset.range cs.length, FastExt.coord (cs.getD k 0) m * x ^ k := by
  rw [evalSpec, sum_range_list, FastExt.coeff_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Ext.algebraMap_eq_ofBase, ← map_pow, mul_comm, ← Algebra.smul_def, Ext.coeff_smul,
    FastExt.coeff_toSpec, mul_comm]

/-- `evalCoord` on the planes of the powers of tabulated base points. -/
theorem evalCoord_tab {B : Nat} (hB : 4 * B < USize.size) (cs : List E) (m : Fin d)
    (xpow : Nat → ByteArray) (g : Nat → F)
    (hx : ∀ k < cs.length - 1, xpow k = encode (tab B fun i ↦ g i ^ (k + 1))) :
    evalCoord cs m B xpow =
      encode (tab B fun i ↦ Ext.coeff (evalSpec cs (Ext.ofBase (g i))) m) := by
  have key : ∀ n ≤ cs.length - 1, (List.range n).foldl (fun acc k ↦
      let s := FastExt.coord (cs.getD (k + 1) 0) m
      if s = 0 then acc else mulAddWords p acc (xpow k) s.val B)
      (replicateWord (FastExt.coord (cs.getD 0 0) m).val B) =
      encode (tab B fun i ↦
        ∑ k ∈ Finset.range (n + 1), FastExt.coord (cs.getD k 0) m * g i ^ k) := by
    intro n hn
    induction n with
    | zero =>
      rw [List.range_zero, List.foldl_nil, replicateWord_tab hB]
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one]
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      dsimp only
      split_ifs with hs
      · refine congrArg encode (tab_congr fun i _ ↦ ?_)
        rw [Finset.sum_range_succ _ (n + 1), hs, zero_mul, add_zero]
      · rw [hx n (by omega), mulAddWords_tab hB]
        refine congrArg encode (tab_congr fun i _ ↦ ?_)
        rw [Finset.sum_range_succ _ (n + 1)]
        ring
  unfold evalCoord
  rw [key _ le_rfl]
  refine congrArg encode (tab_congr fun i _ ↦ ?_)
  rw [coeff_evalSpec]
  rcases Nat.eq_zero_or_pos cs.length with h | h
  · rw [h]
    simp only [Nat.zero_sub, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
      Finset.range_zero, Finset.sum_empty]
    rw [List.getD_eq_default _ _ (by omega), FastExt.coord_zero, Pi.zero_apply]
  · rw [Nat.sub_add_cancel h]

/-- The planes of the powers `x^(j + 1)`. -/
theorem powerPlanes_tab {B : Nat} (hB : 4 * B < USize.size) (g : Nat → F) (k j : Nat)
    (hj : j ≤ k) :
    (powerPlanes p (encode (tab B g)) B k).getD j .empty =
      encode (tab B fun i ↦ g i ^ (j + 1)) := by
  have key : ∀ k, (powerPlanes p (encode (tab B g)) B k).size = k + 1 ∧
      ∀ j ≤ k, (powerPlanes p (encode (tab B g)) B k).getD j .empty =
        encode (tab B fun i ↦ g i ^ (j + 1)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨rfl, fun j hj ↦ ?_⟩
      obtain rfl : j = 0 := by omega
      simp only [powerPlanes, List.range_zero, List.foldl_nil, zero_add, pow_one]
      rfl
    | succ k ih =>
      have e : powerPlanes p (encode (tab B g)) B (k + 1) =
          (powerPlanes p (encode (tab B g)) B k).push (mulWords p
            ((powerPlanes p (encode (tab B g)) B k).getD
              ((powerPlanes p (encode (tab B g)) B k).size - 1) .empty) (encode (tab B g)) B) := by
        simp only [powerPlanes, List.range_succ, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
      obtain ⟨hs, hg⟩ := ih
      rw [e]
      refine ⟨by rw [Array.size_push, hs], fun j hj ↦ ?_⟩
      rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · have := hg j (by omega)
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)] at this
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt (by omega), this]
      · obtain rfl : j = k + 1 := by omega
        rw [Array.getD_eq_getD_getElem?, hs, Nat.add_sub_cancel, hg k le_rfl, mulWords_tab hB,
          ← hs, Array.getElem?_push_size, Option.getD_some]
        refine congrArg encode (tab_congr fun i _ ↦ ?_)
        rw [pow_succ]
  exact (key k).2 j hj

/-- **Inverses of `z - x`** for the base points `x`, `z` outside the base field. -/
theorem invDenoms_rel {B : Nat} (hB : 4 * B < USize.size) {z : E}
    (hz : ∀ x : F, z ≠ FastExt.ofBase x) (g : Nat → F) :
    Rel (invDenoms z (encode (tab B g)) B) (tab B fun i ↦ (z - FastExt.ofBase (g i))⁻¹) := by
  obtain ⟨-, hlen⟩ := evalSpec_adj z 0
  have hd := (FastExt.params (p := p) (E := E)).d_pos
  simp only [FastExt.d] at hlen hd
  have hx : ∀ k < (mulLinear (adjCoeffs z) z).length - 1,
      (powerPlanes p (encode (tab B g)) B (d - 1)).getD k .empty =
        encode (tab B fun i ↦ g i ^ (k + 1)) := fun k hk ↦ by
    rw [length_mulLinear, hlen] at hk
    exact powerPlanes_tab hB g _ k (by simp only [FastExt.d]; omega)
  have hx' : ∀ k < (adjCoeffs z).length - 1,
      (powerPlanes p (encode (tab B g)) B (d - 1)).getD k .empty =
        encode (tab B fun i ↦ g i ^ (k + 1)) := fun k hk ↦
    hx k (by rw [length_mulLinear]; omega)
  -- the norm at every point
  have hN : ∀ x : F, ∃ c : F, c ≠ 0 ∧
      evalSpec (mulLinear (adjCoeffs z) z) (Ext.ofBase x) = Ext.ofBase c ∧
      (FastExt.toSpec z - Ext.ofBase x) * evalSpec (adjCoeffs z) (Ext.ofBase x) =
        Ext.ofBase c := by
    intro x
    have hy : FastExt.toSpec z - Ext.ofBase x ≠ 0 := fun h ↦ hz x (FastExt.toSpec_injective
      (by rw [FastExt.toSpec_ofBase]; exact sub_eq_zero.mp h))
    have hprod : (FastExt.toSpec z - Ext.ofBase x) * evalSpec (adjCoeffs z) (Ext.ofBase x) =
        ∏ j ∈ Finset.range d, (FastExt.toSpec z - Ext.ofBase x) ^ (p ^ j) := by
      rw [(evalSpec_adj z _).1,
        show d = d - 1 + 1 by simp only [FastExt.d]; omega, Finset.prod_range_succ',
        pow_zero, pow_one, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun j _ ↦ (sub_ofBase_pow _ _ _).symm
    refine ⟨Algebra.norm F (FastExt.toSpec z - Ext.ofBase x), fun h0 ↦ ?_, ?_, ?_⟩
    · have := prod_frob_mem (FastExt.toSpec z - Ext.ofBase x)
      rw [h0, Ext.ofBase_zero] at this
      exact Finset.prod_ne_zero_iff.mpr (fun j _ ↦ pow_ne_zero _ hy) this
    · rw [evalSpec_mulLinear, hprod, prod_frob_mem]
    · rw [hprod, prod_frob_mem]
  choose c hc0 hcN hcA using hN
  simp only [invDenoms]
  rw [evalCoord_tab hB _ _ _ g hx]
  have hn : ∀ i, Ext.coeff (evalSpec (mulLinear (adjCoeffs z) z) (Ext.ofBase (g i)))
      ⟨0, (FastExt.params (p := p) (E := E)).d_pos⟩ = c (g i) := fun i ↦ by
    rw [hcN, Ext.coeff_ofBase, ite_eq_left rfl]
  simp only [hn]
  rw [show encode (tab B fun i ↦ c (g i)) = encode (Array.ofFn fun i : Fin B ↦ c (g i)) from rfl,
    batchInvWords_ofFn hB _ fun i ↦ hc0 _]
  refine rel_mk _ _ fun m ↦ ?_
  rw [getElem_ofFn_fin, evalCoord_tab hB _ _ _ g hx',
    show encode (Array.ofFn fun i : Fin B ↦ (c (g i))⁻¹) = encode (tab B fun i ↦ (c (g i))⁻¹)
      from rfl, mulWords_tab hB]
  refine congrArg encode (tab_congr fun i _ ↦ ?_)
  rw [← FastExt.coeff_toSpec, FastExt.toSpec_inv, FastExt.toSpec_sub, FastExt.toSpec_ofBase]
  have hinv : (FastExt.toSpec z - Ext.ofBase (g i))⁻¹ =
      (c (g i))⁻¹ • evalSpec (adjCoeffs z) (Ext.ofBase (g i)) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [mul_smul_comm, hcA, ← Ext.algebraMap_eq_ofBase, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ (hc0 _), map_one]
  rw [hinv, Ext.coeff_smul, mul_comm]

end InvDenoms

end ExtPlanes

/-- Montgomery's batch inversion of the elements (`ExtPlanes.batchInv`) as the inversion of
planes. -/
@[inline, instance_reducible]
def PlanesInv.ofBatch {p : ℕ} [Mont32Field p] {E : Type} [FastExt p E] : PlanesInv p E :=
  ⟨ExtPlanes.batchInv, ExtPlanes.batchInv_rel⟩

end Montgomery.Native32
