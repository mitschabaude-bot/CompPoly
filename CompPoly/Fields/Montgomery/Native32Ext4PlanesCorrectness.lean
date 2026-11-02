/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native32Ext4Planes
public import CompPoly.Fields.Montgomery.Native32WordsCorrectness
public import CompPoly.Fields.Montgomery.InterpolateCosetPackedCorrectness

/-!
# Correctness of the quartic coordinate planes

Planes represent the elements whose coordinates they encode (`Ext4Planes.Rel`). Every plane
operation represents the extension's operation on the represented arrays: sums, differences,
products by base vectors and extension scalars, elementwise products (`mul_rel`), inverses with
zero to zero (`inv_rel`), concatenation of parallel pieces (`join_rel`), and the inverses of
`z - x` for `z` outside the base field (`invDenoms_rel`).
-/

@[expose] public section

namespace Montgomery.Native32.Ext4

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p
local notation "W" => (Binomial4.W : FastField p)

theorem mul_c0 [Binomial4 p] (a b : EF) :
    (a * b).c0 = a.c0 * b.c0 + W * (a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1) := by
  show (Ext4.mul a b).c0 = _
  simp only [Ext4.mul, mulAdd4_eq, Binomial4.mulW_eq]; ring

theorem mul_c1 [Binomial4 p] (a b : EF) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + W * (a.c2 * b.c3 + a.c3 * b.c2) := by
  show (Ext4.mul a b).c1 = _
  simp only [Ext4.mul, mulAdd4_eq, Binomial4.mulW_eq]; ring

theorem mul_c2 [Binomial4 p] (a b : EF) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + W * (a.c3 * b.c3) := by
  show (Ext4.mul a b).c2 = _
  simp only [Ext4.mul, mulAdd4_eq, Binomial4.mulW_eq]; ring

theorem mul_c3 [Binomial4 p] (a b : EF) :
    (a * b).c3 = a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0 := by
  show (Ext4.mul a b).c3 = _
  simp only [Ext4.mul, mulAdd4_eq]

theorem toSpec_ne_zero [Binomial4 p] {a : EF} (h : a ≠ 0) : Ext4.toSpec a ≠ 0 := fun h' ↦
  h (Ext4.toSpec_injective (h'.trans Ext4.toSpec_zero.symm))

theorem smul_eq_ofBase_mul [Binomial4 p] (x : F) (a : EF) :
    Ext4.smul x a = Ext4.ofBase x * a := by
  apply ext' <;> simp only [Ext4.smul, Ext4.ofBase, mul_c0, mul_c1, mul_c2, mul_c3] <;> ring

/-- The coordinates of the products in `F[X] / (X⁴ - W)`. -/
theorem mul_coords [Binomial4 p] (x y : EF) : x * y =
    ⟨x.c0 * y.c0 + W * (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1),
      x.c0 * y.c1 + x.c1 * y.c0 + W * (x.c2 * y.c3 + x.c3 * y.c2),
      x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 + W * (x.c3 * y.c3),
      x.c0 * y.c3 + x.c1 * y.c2 + x.c2 * y.c1 + x.c3 * y.c0⟩ := by
  apply ext' <;>
    simp only [show x * y = Montgomery.Native32.Ext4.mul x y from rfl, Montgomery.Native32.Ext4.mul,
      Binomial4.mulW_eq, mulAdd4_eq] <;> ring

theorem mul_ofBase [Binomial4 p] (a : EF) (x : F) : a * Ext4.ofBase x = Ext4.smul x a := by
  apply ext' <;>
    simp only [mul_c0, mul_c1, mul_c2, mul_c3, Ext4.ofBase, Ext4.smul] <;>
    ring

theorem mul_comm' [Binomial4 p] (a b : EF) : a * b = b * a := by
  rw [Ext4.mul_coords, Ext4.mul_coords]
  congr 1 <;> ring

theorem add_zero' (a : EF) : a + 0 = a := by
  show (⟨a.c0 + 0, a.c1 + 0, a.c2 + 0, a.c3 + 0⟩ : EF) = a
  simp only [add_zero]

theorem mul_ofBase_zero [Binomial4 p] (a : EF) : a * Ext4.ofBase 0 = 0 := by
  rw [Ext4.mul_coords]
  simp only [ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3, MulZeroClass.mul_zero, add_zero]
  rfl
/-- `(z - x)⁻¹ = (b₀ + t b₁ + t² b₂ + t³) / N` for `t = z₀ - x` and `N` the norm of `z - x`. -/
theorem inv_sub_ofBase [Binomial4 p] (z : EF) (x : F) :
    (z - ofBase x)⁻¹ =
      let t := z.c0 - x
      smul (normAt (normK0 z) (normK1 z) (z.c2 + z.c2) t (t * t))⁻¹
        (adj0 z + smul t (adj1 z) + smul (t * t) (adj2 z) + ofBase (t * t * t)) := by
  rw [show (z - ofBase x)⁻¹ = inv (z - ofBase x) from rfl]
  unfold inv
  rw [norm_sub_ofBase]
  apply ext' <;>
    simp only [adj0, adj1, adj2, g0, g1, twoW, normK0, normK1, Binomial4.mulW_eq, add_c0, add_c1,
      add_c2, add_c3, sub_c0, sub_c1, sub_c2, sub_c3, ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3,
      smul_c0, smul_c1, smul_c2, smul_c3] <;>
    ring

/-- For `z` outside the base field, the norm of `z - x` is not zero. -/
theorem normAt_ne_zero [Binomial4 p] {z : EF} (hz : z.c1 ≠ 0 ∨ z.c2 ≠ 0 ∨ z.c3 ≠ 0) (x : F) :
    normAt (normK0 z) (normK1 z) (z.c2 + z.c2) (z.c0 - x) ((z.c0 - x) * (z.c0 - x)) ≠ 0 := by
  rw [← norm_sub_ofBase]
  refine norm_ne_zero _ (toSpec_ne_zero fun h ↦ ?_)
  have h1 := congrArg c1 h
  have h2 := congrArg c2 h
  have h3 := congrArg c3 h
  simp only [sub_c1, sub_c2, sub_c3, ofBase_c1, ofBase_c2, ofBase_c3, sub_zero] at h1 h2 h3
  rcases hz with h | h | h
  · exact h h1
  · exact h h2
  · exact h h3

end Montgomery.Native32.Ext4

namespace Montgomery.Native32.Ext4Planes
open CompPoly.PackedRepr (encode)
open CompPoly.CPolynomial.NTTFast.Packed (size_encode_fields getD_ofFn_bounded ofWord_val)
open CompPoly.CPolynomial.NTTFast.Packed.Native (zeroWords)
open CompPoly.CPolynomial.NTTFast.Packed (Native.encodeFields_eq)
open Words

variable {p : ℕ} [Mont32Field p]

local notation "F" => FastField p
local notation "EF" => Ext4 p
local notation "W" => (Binomial4.W : FastField p)

/-- Planes represent the elements whose coordinates they encode. -/
def Rel (v : Ext4Planes p) (a : Array EF) : Prop :=
  v.n = a.size ∧ v.c0 = encode (a.map (·.c0)) ∧ v.c1 = encode (a.map (·.c1)) ∧
    v.c2 = encode (a.map (·.c2)) ∧ v.c3 = encode (a.map (·.c3))

/-- An in-range coordinate of an array of extension elements. -/
theorem getD_map (a : Array EF) (pr : EF → F) (i : Nat) (h : i < a.size) :
    (a.map pr).getD i 0 = pr a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem h]
  rfl

/-- Planes of tabulated coordinates represent the elements with those coordinates. -/
theorem rel_mk {n : Nat} {P0 P1 P2 P3 : ByteArray} (c : Array EF) (hn : c.size = n)
    (f0 f1 f2 f3 : Nat → F)
    (h0 : P0 = encode (Array.ofFn (n := n) fun i ↦ f0 i.val))
    (h1 : P1 = encode (Array.ofFn (n := n) fun i ↦ f1 i.val))
    (h2 : P2 = encode (Array.ofFn (n := n) fun i ↦ f2 i.val))
    (h3 : P3 = encode (Array.ofFn (n := n) fun i ↦ f3 i.val))
    (hc : ∀ i (h : i < c.size), c[i] = ⟨f0 i, f1 i, f2 i, f3 i⟩) :
    Rel ⟨n, P0, P1, P2, P3⟩ c := by
  subst hn
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [h0, h1, h2, h3]
    congr 1
    apply Array.ext (by rw [Array.size_ofFn, Array.size_map])
    intro i hi _
    rw [Array.size_ofFn] at hi
    simp only [Array.getElem_ofFn, Array.getElem_map, hc i hi]

/-- A plane is its tabulated coordinates. -/
theorem encode_map (a : Array EF) (pr : EF → F) :
    encode (a.map pr) = encode (Array.ofFn (n := a.size) fun i ↦ (a.map pr).getD i.val 0) := by
  congr 1
  apply Array.ext (by rw [Array.size_ofFn, Array.size_map])
  intro i hi _
  rw [Array.size_map] at hi
  simp only [Array.getElem_ofFn, getD_map a pr i hi, Array.getElem_map]

/-- Represented, indexable planes read back their elements. -/
theorem toArray_eq {v : Ext4Planes p} {a : Array EF} (hv : Rel v a)
    (hs : 4 * a.size < USize.size) : v.toArray = a := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  have hm : ∀ pr : EF → F, 4 * (a.map pr).size < USize.size := fun pr ↦ by
    rw [Array.size_map]; exact hs
  apply Array.ext (by rw [Ext4Planes.toArray, Array.size_ofFn, hvn])
  intro i hi _
  rw [Ext4Planes.toArray, Array.size_ofFn, hvn] at hi
  have hm' : ∀ pr : EF → F, i < (a.map pr).size := fun pr ↦ by rw [Array.size_map]; exact hi
  simp only [Ext4Planes.toArray, Array.getElem_ofFn, Ext4Planes.get, h0, h1, h2, h3,
    read_encode _ _ (hm _) (hm' _),  ofWord_val, getD_map a _ i hi]

/-- The planes of an array represent it. -/
theorem ofArray_rel (a : Array EF) : Rel (Ext4Planes.ofArray a) a := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> exact Native.encodeFields_eq _

/-- Zero planes represent zeros. -/
theorem zeros_rel (n : Nat) : Rel (zeros (p := p) n) (Array.replicate n 0) := by
  refine ⟨(Array.size_replicate ..).symm, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [zeros, zeroWords_eq (p := p), Array.map_replicate]
    rfl

/-- Elementwise sums. -/
theorem add_rel {v w : Ext4Planes p} {a b : Array EF} (hv : Rel v a) (hw : Rel w b) (hn : v.n = w.n)
    (hs : 4 * a.size < USize.size) : Rel (v.add w) (Array.zipWith (· + ·) a b) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  obtain ⟨hwn, g0, g1, g2, g3⟩ := hw
  have hb : 4 * b.size < USize.size := by omega
  have hab : a.size = b.size := by omega
  unfold Ext4Planes.add
  rw [h0, h1, h2, h3, g0, g1, g2, g3, hvn]
  refine rel_mk _ (by rw [Array.size_zipWith, hab, Nat.min_self])
    (fun i ↦ (a.map (·.c0)).getD i 0 + (b.map (·.c0)).getD i 0)
    (fun i ↦ (a.map (·.c1)).getD i 0 + (b.map (·.c1)).getD i 0)
    (fun i ↦ (a.map (·.c2)).getD i 0 + (b.map (·.c2)).getD i 0)
    (fun i ↦ (a.map (·.c3)).getD i 0 + (b.map (·.c3)).getD i 0)
    ?_ ?_ ?_ ?_ fun i hi ↦ ?_
  all_goals try (apply addWords_encode <;> simp only [Array.size_map] <;> omega)
  rw [Array.size_zipWith] at hi
  simp only [Array.getElem_zipWith, getD_map a _ i (by omega), getD_map b _ i (by omega)]
  rfl

/-- Elementwise differences. -/
theorem sub_rel {v w : Ext4Planes p} {a b : Array EF} (hv : Rel v a) (hw : Rel w b) (hn : v.n = w.n)
    (hs : 4 * a.size < USize.size) : Rel (v.sub w) (Array.zipWith (· - ·) a b) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  obtain ⟨hwn, g0, g1, g2, g3⟩ := hw
  have hb : 4 * b.size < USize.size := by omega
  have hab : a.size = b.size := by omega
  unfold Ext4Planes.sub
  rw [h0, h1, h2, h3, g0, g1, g2, g3, hvn]
  refine rel_mk _ (by rw [Array.size_zipWith, hab, Nat.min_self])
    (fun i ↦ (a.map (·.c0)).getD i 0 - (b.map (·.c0)).getD i 0)
    (fun i ↦ (a.map (·.c1)).getD i 0 - (b.map (·.c1)).getD i 0)
    (fun i ↦ (a.map (·.c2)).getD i 0 - (b.map (·.c2)).getD i 0)
    (fun i ↦ (a.map (·.c3)).getD i 0 - (b.map (·.c3)).getD i 0)
    ?_ ?_ ?_ ?_ fun i hi ↦ ?_
  all_goals try (apply subWords_encode <;> simp only [Array.size_map] <;> omega)
  rw [Array.size_zipWith] at hi
  simp only [Array.getElem_zipWith, getD_map a _ i (by omega), getD_map b _ i (by omega)]
  rfl

/-- An in-range entry of a constant array. -/
theorem getD_replicate (n : Nat) (x : F) (i : Nat) (h : i < n) :
    (Array.replicate n x).getD i 0 = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, ite_eq_left_of_eq_true _ _
    (eq_true h), Option.getD_some]

/-- A scalar minus every element. -/
theorem rsub_rel {v : Ext4Planes p} {a : Array EF} (s : EF) (hv : Rel v a)
    (hs : 4 * a.size < USize.size) : Rel (rsub s v) (a.map (s - ·)) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  unfold Ext4Planes.rsub
  have hr : 4 * v.n < USize.size := by omega
  rw [replicateWord_encode _ _ hr, replicateWord_encode _ _ hr, replicateWord_encode _ _ hr,
    replicateWord_encode _ _ hr, h0, h1, h2, h3, hvn]
  refine rel_mk _ (by rw [Array.size_map])
    (fun i ↦ (Array.replicate a.size s.c0).getD i 0 - (a.map (·.c0)).getD i 0)
    (fun i ↦ (Array.replicate a.size s.c1).getD i 0 - (a.map (·.c1)).getD i 0)
    (fun i ↦ (Array.replicate a.size s.c2).getD i 0 - (a.map (·.c2)).getD i 0)
    (fun i ↦ (Array.replicate a.size s.c3).getD i 0 - (a.map (·.c3)).getD i 0)
    ?_ ?_ ?_ ?_ fun i hi ↦ ?_
  all_goals try (apply subWords_encode <;> simp only [Array.size_map, Array.size_replicate] <;>
    omega)
  rw [Array.size_map] at hi
  simp only [Array.getElem_map, getD_map a _ i hi, getD_replicate _ _ i hi]
  rfl

/-- Every element times a base element. -/
theorem mulBase_rel [Binomial4 p] {v : Ext4Planes p} {a : Array EF} (bs : Array F)
    (hv : Rel v a)
    (hb : a.size ≤ bs.size) (hs : 4 * bs.size < USize.size) :
    Rel (v.mulBase (encode bs)) (Array.zipWith (fun x y ↦ x * Ext4.ofBase y) a bs) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  unfold Ext4Planes.mulBase
  rw [h0, h1, h2, h3, hvn]
  refine rel_mk _ (by rw [Array.size_zipWith, Nat.min_eq_left hb])
    (fun i ↦ (a.map (·.c0)).getD i 0 * bs.getD i 0)
    (fun i ↦ (a.map (·.c1)).getD i 0 * bs.getD i 0)
    (fun i ↦ (a.map (·.c2)).getD i 0 * bs.getD i 0)
    (fun i ↦ (a.map (·.c3)).getD i 0 * bs.getD i 0)
    ?_ ?_ ?_ ?_ fun i hi ↦ ?_
  all_goals try (apply mulWords_encode <;> (try simp only [Array.size_map]) <;> omega)
  rw [Array.size_zipWith] at hi
  simp only [Array.getElem_zipWith, getD_map a _ i (by omega), Ext4.mul_coords, Ext4.ofBase,
    Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem
      (show i < bs.size by omega), Option.getD_some]
  congr 1 <;> ring

/-- `∑ⱼ Xⱼ · sⱼ` for four planes. -/
theorem combine4_encode (n : Nat) (X0 X1 X2 X3 : Array F) (s0 s1 s2 s3 : F)
    (h0 : n ≤ X0.size) (h1 : n ≤ X1.size) (h2 : n ≤ X2.size) (h3 : n ≤ X3.size)
    (g0 : 4 * X0.size < USize.size) (g1 : 4 * X1.size < USize.size)
    (g2 : 4 * X2.size < USize.size) (g3 : 4 * X3.size < USize.size) :
    combine p n [(encode X0, s0.val), (encode X1, s1.val), (encode X2, s2.val),
      (encode X3, s3.val)] = encode (Array.ofFn (n := n) fun i ↦ X0.getD i.val 0 * s0 +
        X1.getD i.val 0 * s1 + X2.getD i.val 0 * s2 + X3.getD i.val 0 * s3) := by
  have hn : 4 * n < USize.size := by omega
  simp only [combine, List.foldl_cons, List.foldl_nil, zeroWords_eq (p := p)]
  rw [mulAddWords_encode _ _ _ _ (by rw [Array.size_replicate]) h0
      (by rw [Array.size_replicate]; exact hn) g0,
    mulAddWords_encode _ _ _ _ (by rw [Array.size_ofFn]) h1 (by rw [Array.size_ofFn]; exact hn) g1,
    mulAddWords_encode _ _ _ _ (by rw [Array.size_ofFn]) h2 (by rw [Array.size_ofFn]; exact hn) g2,
    mulAddWords_encode _ _ _ _ (by rw [Array.size_ofFn]) h3 (by rw [Array.size_ofFn]; exact hn) g3]
  refine congrArg encode (congrArg (Array.ofFn (n := n)) (funext fun i ↦ ?_))
  simp only [getD_ofFn_bounded _ _ i.isLt, getD_replicate _ _ _ i.isLt, zero_add]

/-- Every element times an extension scalar. -/
theorem smul_rel [Binomial4 p] {v : Ext4Planes p} {a : Array EF} (s : EF) (hv : Rel v a)
    (hs : 4 * a.size < USize.size) : Rel (v.smul s) (a.map (· * s)) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  unfold Ext4Planes.smul
  simp only [h0, h1, h2, h3, hvn]
  have hm : ∀ pr : EF → F, a.size ≤ (a.map pr).size := fun pr ↦ by rw [Array.size_map]
  have hm' : ∀ pr : EF → F, 4 * (a.map pr).size < USize.size := fun pr ↦ by
    rw [Array.size_map]; exact hs
  rw [combine4_encode _ _ _ _ _ _ _ _ _ (hm _) (hm _) (hm _) (hm _) (hm' _) (hm' _) (hm' _)
      (hm' _), combine4_encode _ _ _ _ _ _ _ _ _ (hm _) (hm _) (hm _) (hm _) (hm' _) (hm' _)
      (hm' _) (hm' _), combine4_encode _ _ _ _ _ _ _ _ _ (hm _) (hm _) (hm _) (hm _) (hm' _)
      (hm' _) (hm' _) (hm' _), combine4_encode _ _ _ _ _ _ _ _ _ (hm _) (hm _) (hm _) (hm _)
      (hm' _) (hm' _) (hm' _) (hm' _)]
  let A (pr : EF → F) (i : Nat) : F := (a.map pr).getD i 0
  refine rel_mk _ (Array.size_map ..)
    (fun i ↦ A (·.c0) i * s.c0 + A (·.c1) i * (Binomial4.mulW s.c3) + A (·.c2) i *
        (Binomial4.mulW s.c2) +
      A (·.c3) i * (Binomial4.mulW s.c1))
    (fun i ↦ A (·.c0) i * s.c1 + A (·.c1) i * s.c0 + A (·.c2) i * (Binomial4.mulW s.c3) +
      A (·.c3) i * (Binomial4.mulW s.c2))
    (fun i ↦ A (·.c0) i * s.c2 + A (·.c1) i * s.c1 + A (·.c2) i * s.c0 +
      A (·.c3) i * (Binomial4.mulW s.c3))
    (fun i ↦ A (·.c0) i * s.c3 + A (·.c1) i * s.c2 + A (·.c2) i * s.c1 + A (·.c3) i * s.c0)
    rfl rfl rfl rfl fun i hi ↦ ?_
  rw [Array.size_map] at hi
  simp only [A, Array.getElem_map, getD_map a _ i hi, Ext4.mul_coords, Binomial4.mulW_eq]
  congr 1 <;> ring

/-- A plane as tabulated coordinates. -/
theorem encode_map_eq (a : Array EF) (pr : EF → F) (n : Nat) (h : a.size = n) :
    encode (a.map pr) = encode (Array.ofFn (n := n) fun i ↦ pr (a[i.val]'(by omega))) := by
  subst h
  congr 1
  apply Array.ext (by rw [Array.size_ofFn, Array.size_map])
  intro i _ _
  simp only [Array.getElem_ofFn, Array.getElem_map]

/-- Planes of tabulated coordinates represent the elements with those coordinates. -/
theorem rel_ofFn {n : Nat} (c : Array EF) (hn : c.size = n) (f0 f1 f2 f3 : Fin n → F)
    (hc : ∀ i : Fin n, c[i.val]'(by omega) = ⟨f0 i, f1 i, f2 i, f3 i⟩) :
    Rel ⟨n, encode (Array.ofFn f0), encode (Array.ofFn f1), encode (Array.ofFn f2),
      encode (Array.ofFn f3)⟩ c := by
  subst hn
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
  · refine congrArg encode ?_
    apply Array.ext (by rw [Array.size_ofFn, Array.size_map])
    intro i hi _
    rw [Array.size_ofFn] at hi
    simp only [Array.getElem_ofFn, Array.getElem_map, hc ⟨i, hi⟩]

/-- Elementwise products. -/
theorem mul_rel [Binomial4 p] {v w : Ext4Planes p} {a b : Array EF} (hv : Rel v a) (hw : Rel w b)
    (hn : v.n = w.n)
    (hs : 4 * a.size < USize.size) : Rel (v.mul w) (Array.zipWith (· * ·) a b) := by
  obtain ⟨hvn, h0, h1, h2, h3⟩ := hv
  obtain ⟨hwn, g0, g1, g2, g3⟩ := hw
  have hab : b.size = a.size := by omega
  simp only [Ext4Planes.mul, h0, h1, h2, h3, g0, g1, g2, g3, hvn, List.foldl_cons, List.foldl_nil]
  simp only [zeroWords_ofFn (p := p), encode_map_eq a _ a.size rfl, encode_map_eq b _ a.size hab]
  simp only [mulWords_ofFn hs]
  simp only [addWords_ofFn hs]
  simp only [mulAddWords_ofFn hs]
  refine rel_ofFn (n := a.size) (Array.zipWith (· * ·) a b) ?_ _ _ _ _ ?_
  · rw [Array.size_zipWith, hab, Nat.min_self]
  intro i
  simp only [Array.getElem_zipWith, Ext4.mul_coords]
  generalize a[i.val] = x
  generalize b[i.val]'(by omega) = y
  simp only [Montgomery.Native32.Ext4.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- Planes represent tabulated elements when they tabulate the coordinates. -/
theorem rel_tab_iff {B : Nat} {v : Ext4Planes p} {f : Nat → EF} :
    Rel v (tab B f) ↔ v.n = B ∧ v.c0 = encode (tab B fun i ↦ (f i).c0) ∧
      v.c1 = encode (tab B fun i ↦ (f i).c1) ∧ v.c2 = encode (tab B fun i ↦ (f i).c2) ∧
      v.c3 = encode (tab B fun i ↦ (f i).c3) := by
  simp only [Rel, size_tab, tab_map]

theorem Rel.congr_tab {B : Nat} {v : Ext4Planes p} {f g : Nat → EF} (h : Rel v (tab B f))
    (hfg : ∀ i < B, f i = g i) : Rel v (tab B g) := by
  rw [← tab_congr hfg]; exact h

/-- **Inverses of planes**: `Ext4.inv` coordinate by coordinate, zero to zero. -/
theorem inv_rel [Binomial4 p] {B : Nat} (hB : 4 * B < USize.size) {v : Ext4Planes p}
    {f : Nat → EF} (hv : Rel v (tab B f)) : Rel v.inv (tab B fun i ↦ (f i)⁻¹) := by
  obtain ⟨hn, h0, h1, h2, h3⟩ := rel_tab_iff.mp hv
  unfold inv
  simp only [hn, h0, h1, h2, h3, mulWords_tab hB, addWords_tab hB, subWords_tab hB,
    mulAddWords_tab hB, scaleWords_tab hB, invWords_tab hB]
  refine rel_tab_iff.mpr ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
  · refine congrArg encode (tab_congr fun i _ ↦ ?_)
    first
      | show _ = (Ext4.inv (f i)).c0
      | show _ = (Ext4.inv (f i)).c1
      | show _ = (Ext4.inv (f i)).c2
      | show _ = (Ext4.inv (f i)).c3
    simp only [Ext4.inv, Ext4.g0, Ext4.g1, Ext4.norm, Binomial4.mulW_eq]
    ring

/-- Planes of parallel pieces, concatenated. -/
theorem join_rel (n parts : Nat) (V : Nat → Ext4Planes p) (A : Nat → Array EF)
    (hV : ∀ k < parts, Rel (V k) (A k))
    (hn : n = ((List.range parts).foldl (fun acc k ↦ acc ++ A k) #[]).size) :
    Rel (join p n ((Array.range parts).map fun k ↦ Task.spawn fun _ ↦ #[(V k).c0, (V k).c1,
      (V k).c2, (V k).c3])) ((List.range parts).foldl (fun acc k ↦ acc ++ A k) #[]) := by
  unfold join
  simp only [← Array.foldl_toList, Array.toList_map, List.foldl_map, Array.toList_range,
    get_spawn]
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · refine (foldl_bytes parts _ (fun k ↦ (A k).map (·.c0)) fun k hk ↦ (hV k hk).2.1).trans ?_
    rw [← foldl_append_map, Array.map_empty]
  · refine (foldl_bytes parts _ (fun k ↦ (A k).map (·.c1)) fun k hk ↦ (hV k hk).2.2.1).trans ?_
    rw [← foldl_append_map, Array.map_empty]
  · refine (foldl_bytes parts _ (fun k ↦ (A k).map (·.c2)) fun k hk ↦ (hV k hk).2.2.2.1).trans ?_
    rw [← foldl_append_map, Array.map_empty]
  · refine (foldl_bytes parts _ (fun k ↦ (A k).map (·.c3)) fun k hk ↦ (hV k hk).2.2.2.2).trans ?_
    rw [← foldl_append_map, Array.map_empty]


/-- `invDenoms` inverts `z - x` for every base point `x`, for `z` outside the base field. -/
theorem invDenoms_rel [Binomial4 p] {z : EF} (hz : z.c1 ≠ 0 ∨ z.c2 ≠ 0 ∨ z.c3 ≠ 0)
    (X : Array F) (hs : 4 * X.size < USize.size) :
    Rel (invDenoms z (encode X) X.size) (X.map fun x ↦ (z - Ext4.ofBase x)⁻¹) := by
  simp only [invDenoms]
  rw [encode_ofFn_getElem X]
  simp only [mulWords_ofFn hs, addWords_ofFn hs, subWords_ofFn hs, mulAddWords_ofFn hs,
    replicateWord_ofFn hs]
  rw [batchInvWords_ofFn hs _ ?_]
  · simp only [mulWords_ofFn hs]
    refine rel_ofFn _ (Array.size_map ..) _ _ _ _ fun i ↦ ?_
    rw [Array.getElem_map, Ext4.inv_sub_ofBase]
    apply Ext4.ext' <;>
      simp only [Ext4.normAt, Binomial4.mulW_eq, Ext4.add_c0, Ext4.add_c1, Ext4.add_c2,
        Ext4.add_c3, Ext4.smul_c0, Ext4.smul_c1, Ext4.smul_c2, Ext4.smul_c3, Ext4.ofBase_c0,
        Ext4.ofBase_c1, Ext4.ofBase_c2, Ext4.ofBase_c3] <;> ring
  · intro i
    have := Ext4.normAt_ne_zero hz X[i.val]
    simp only [Ext4.normAt, Binomial4.mulW_eq] at this
    convert this using 1
    ring

end Montgomery.Native32.Ext4Planes
