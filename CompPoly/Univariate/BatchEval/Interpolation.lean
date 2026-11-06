/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import all CompPoly.Univariate.BatchEval.Correctness
public import CompPoly.Univariate.BatchEval.Correctness
public import CompPoly.Univariate.Deriv
public import CompPoly.Univariate.LagrangeArray
public import CompPoly.Univariate.ToPoly.RingHom
public import CompPoly.Data.List.BatchInv

/-!
# Subproduct-Tree Interpolation

Fast interpolation on arbitrary distinct nodes, reusing the subproduct tree of
`BatchEval/SubproductTree.lean`. With `G = ∏ (X - xᵢ)` at the root, the interpolant of the
values `yᵢ` is

  `∑ᵢ cᵢ · G / (X - xᵢ)`, where `cᵢ = yᵢ / G'(xᵢ)`,

and both halves run over the tree. Descending with `G'` gives the denominators, which are
batch-inverted with one field inversion. The sum is then assembled bottom-up as
`L · M_right + R · M_left` at each node. With an NTT-backed `MulContext` this is the
classical `O(M(n) log n)` algorithm; it needs no root of unity and no power-of-two size.

## Main definitions

* `SubproductTree.interpolateWeights`: recombination of the precomputed leaf weights.
* `interpolateSubproduct`: interpolation of values on an array of nodes.

## Main results

* `interpolateSubproduct_eq_interpolateArrays`: for pairwise distinct nodes, the result is
  the Lagrange interpolant `CLagrange.interpolateArrays`.
-/

@[expose] public section

namespace CompPoly
namespace CPolynomial

variable {R : Type*}

namespace SubproductTree

/-- The number of leaves of a subproduct tree. -/
def leafCount [Zero R] : SubproductTree R → Nat
  | leaf _ _ => 1
  | node _ left right => leafCount left + leafCount right

/-- Recombine interpolation weights against the sibling product polynomials. -/
def interpolateWeights [Field R] [BEq R] [LawfulBEq R] (M : MulContext R) :
    SubproductTree R → List R → CPolynomial R
  | leaf _ _, ws => C (ws.headD 0)
  | node _ left right, ws =>
      M.mul right.poly (interpolateWeights M left (ws.take (leafCount left))) +
        M.mul left.poly (interpolateWeights M right (ws.drop (leafCount left)))

end SubproductTree

/-- Interpolate the values `ys` on the nodes `xs` through a subproduct tree.

Missing values default to `0`, as in `CLagrange.interpolateArrays`. -/
def interpolateSubproduct [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) (D : ModContext R) (xs ys : Array R) : CPolynomial R :=
  match SubproductTree.buildArray M xs with
  | none => 0
  | some tree =>
      let ds := SubproductTree.evalList D (derivative tree.poly) tree
      let ws := (List.ofFn fun i : Fin xs.size => ys.getD i 0).zipWith (· * ·)
        (CompPoly.List.batchInv ds)
      SubproductTree.interpolateWeights M tree ws

/-! ### Correctness -/

namespace SubproductTree

section Correctness

variable [Field R]

private theorem leafCount_eq_length_points :
    ∀ tree : SubproductTree R, leafCount tree = (points tree).length
  | leaf _ _ => rfl
  | node _ left right => by
      simp [leafCount, points, leafCount_eq_length_points left,
        leafCount_eq_length_points right]

/-- A product of linear factors vanishes at each of its roots. -/
private theorem eval_prod_X_sub_C_of_mem {l : List R} {x : R} (hx : x ∈ l) :
    ((l.map fun q => Polynomial.X - Polynomial.C q).prod).eval x = 0 := by
  rw [Polynomial.eval_list_prod, List.map_map]
  exact List.prod_eq_zero (List.mem_map.mpr ⟨x, hx, by simp⟩)

private theorem eval_prod_X_sub_C (l : List R) (x : R) :
    ((l.map fun q => Polynomial.X - Polynomial.C q).prod).eval x =
      (l.map fun q => x - q).prod := by
  rw [Polynomial.eval_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  simp

private theorem degree_prod_X_sub_C :
    ∀ l : List R,
      ((l.map fun q => Polynomial.X - Polynomial.C q).prod).degree = (l.length : WithBot ℕ)
  | [] => by simp
  | a :: l => by
      rw [List.map_cons, List.prod_cons, Polynomial.degree_mul, Polynomial.degree_X_sub_C,
        degree_prod_X_sub_C l, List.length_cons, Nat.cast_succ, add_comm]

/-- The derivative of `∏ (X - qⱼ)` at the root `qᵢ` is `∏_{j ≠ i} (qᵢ - qⱼ)`. -/
private theorem eval_derivative_prod_X_sub_C :
    ∀ (l : List R) (i : ℕ) (hi : i < l.length),
      (Polynomial.derivative ((l.map fun q => Polynomial.X - Polynomial.C q).prod)).eval l[i] =
        ((l.eraseIdx i).map fun q => l[i] - q).prod
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | a :: l, 0, _ => by
      simp only [List.map_cons, List.prod_cons, Polynomial.derivative_mul,
        Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
        one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, List.getElem_cons_zero, sub_self,
        List.eraseIdx_cons_zero]
      rw [eval_prod_X_sub_C l a]
      ring
  | a :: l, i + 1, hi => by
      have hi' : i < l.length := by simpa using hi
      simp only [List.map_cons, List.prod_cons, Polynomial.derivative_mul,
        Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
        one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, List.getElem_cons_succ, List.eraseIdx_cons_succ]
      rw [eval_prod_X_sub_C_of_mem (List.getElem_mem hi'), zero_add,
        eval_derivative_prod_X_sub_C l i hi']

/-- Every stored polynomial is the product of its children's, with `X - C x` at a leaf. -/
private def IsExact : SubproductTree R → Prop
  | leaf x p => p.toPoly = Polynomial.X - Polynomial.C x
  | node p left right => p.toPoly = left.poly.toPoly * right.poly.toPoly ∧
      IsExact left ∧ IsExact right

private theorem toPoly_poly_of_exact :
    ∀ {tree : SubproductTree R}, IsExact tree →
      tree.poly.toPoly = ((points tree).map fun q => Polynomial.X - Polynomial.C q).prod
  | leaf x p, h => by simpa [poly, points, IsExact] using h
  | node p left right, h => by
      rw [poly, h.1, toPoly_poly_of_exact h.2.1, toPoly_poly_of_exact h.2.2]
      simp [points]

variable [BEq R] [LawfulBEq R]

private theorem exact_leafFor (x : R) : IsExact (leafFor x) := by
  change (linearFactor x).toPoly = _
  rw [linearFactor, toPoly_add, C_toPoly, X_toPoly, Polynomial.C_neg]
  ring

private theorem exact_combine (M : MulContext R) {left right : SubproductTree R}
    (hleft : IsExact left) (hright : IsExact right) : IsExact (combine M left right) :=
  ⟨by rw [M.mul_eq_mul, toPoly_mul], hleft, hright⟩

private theorem exact_combinePairs (M : MulContext R) :
    ∀ {trees : List (SubproductTree R)}, List.Forall IsExact trees →
      List.Forall IsExact (combinePairs M trees)
  | [], _ => by simp [combinePairs]
  | [_], h => by simpa [combinePairs] using h
  | left :: right :: rest, h => by
      simp only [combinePairs, List.forall_cons] at h ⊢
      exact ⟨exact_combine M h.1 h.2.1, exact_combinePairs M h.2.2⟩

private theorem exact_buildFromTrees (M : MulContext R) :
    ∀ (fuel : ℕ) (trees : List (SubproductTree R)) (tree : SubproductTree R),
      buildFromTrees M fuel trees = some tree → List.Forall IsExact trees → IsExact tree := by
  intro fuel
  induction fuel with
  | zero =>
      intro trees tree hbuild hexact
      match trees, hbuild with
      | [head], hbuild =>
          simp only [buildFromTrees, Option.some.injEq] at hbuild
          subst hbuild
          simpa using hexact
  | succ fuel ih =>
      intro trees tree hbuild hexact
      match trees, hbuild with
      | [head], hbuild =>
          simp only [buildFromTrees, Option.some.injEq] at hbuild
          subst hbuild
          simpa using hexact
      | head :: second :: rest, hbuild =>
          exact ih _ tree (by simpa [buildFromTrees] using hbuild)
            (exact_combinePairs M hexact)

private theorem exact_buildArray (M : MulContext R) {xs : Array R} {tree : SubproductTree R}
    (hbuild : buildArray M xs = some tree) : IsExact tree := by
  refine exact_buildFromTrees M _ (xs.toList.map leafFor) tree
    (by simpa [buildArray, buildList] using hbuild) ?_
  simp only [List.forall_iff_forall_mem, List.mem_map]
  rintro _ ⟨x, _, rfl⟩
  exact exact_leafFor x

/-- The contract of `interpolateWeights` on an exact tree: its degree is below the leaf count,
and at the `i`-th leaf it takes `yᵢ · ∏_{j ≠ i} (xᵢ - xⱼ)`. -/
private theorem interpolateWeights_spec (M : MulContext R) :
    ∀ (tree : SubproductTree R), IsExact tree →
      ∀ (ys : List R) (_hlen : ys.length = (points tree).length),
        (interpolateWeights M tree ys).toPoly.degree < (points tree).length ∧
        ∀ (i : ℕ) (hi : i < (points tree).length),
          (interpolateWeights M tree ys).toPoly.eval (points tree)[i] =
            ys[i]'(by omega) *
              (((points tree).eraseIdx i).map fun q => (points tree)[i] - q).prod
  | leaf x p, _, ys, hlen => by
      obtain ⟨y, rfl⟩ : ∃ y, ys = [y] := by
        match ys, hlen with
        | [y], _ => exact ⟨y, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [interpolateWeights, C_toPoly]
        exact (Polynomial.degree_C_le).trans_lt (by simp [points])
      · intro i hi
        have hi0 : i = 0 := by simpa [points] using hi
        subst hi0
        simp [interpolateWeights, points, C_toPoly]
  | node p left right, hexact, ys, hlen => by
      obtain ⟨_, hleft, hright⟩ := hexact
      have hcount : leafCount left = (points left).length := leafCount_eq_length_points left
      have hlen' : ys.length = (points left).length + (points right).length := by
        simpa [points] using hlen
      have hL := interpolateWeights_spec M left hleft
        (ys.take (leafCount left)) (by simp [hcount, hlen'])
      have hR := interpolateWeights_spec M right hright
        (ys.drop (leafCount left)) (by simp [hcount, hlen'])
      have hPl := toPoly_poly_of_exact hleft
      have hPr := toPoly_poly_of_exact hright
      have htoPoly : (interpolateWeights M (node p left right) ys).toPoly =
          (interpolateWeights M left
              (ys.take (leafCount left))).toPoly * right.poly.toPoly +
            (interpolateWeights M right
              (ys.drop (leafCount left))).toPoly * left.poly.toPoly := by
        simp only [interpolateWeights, M.mul_eq_mul, toPoly_add, toPoly_mul]
        ring
      rw [htoPoly]
      simp only [points]
      refine ⟨?_, ?_⟩
      · refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
        · rw [Polynomial.degree_mul, hPr, degree_prod_X_sub_C, List.length_append,
            Nat.cast_add]
          exact WithBot.add_lt_add_right WithBot.coe_ne_bot hL.1
        · rw [Polynomial.degree_mul, hPl, degree_prod_X_sub_C, List.length_append,
            Nat.cast_add, add_comm ((points left).length : WithBot ℕ)]
          exact WithBot.add_lt_add_right WithBot.coe_ne_bot hR.1
      · intro i hi
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul]
        by_cases hil : i < (points left).length
        · have hroot : left.poly.toPoly.eval (points left)[i] = 0 := by
            rw [hPl]
            exact eval_prod_X_sub_C_of_mem (List.getElem_mem hil)
          have hx : (points left ++ points right)[i] = (points left)[i] :=
            List.getElem_append_left hil
          rw [hx, hL.2 i hil, hroot]
          simp only [hPr, eval_prod_X_sub_C,
            List.eraseIdx_append_of_lt_length hil, List.map_append, List.prod_append,
            List.getElem_take]
          ring
        · have hle : (points left).length ≤ i := Nat.le_of_not_lt hil
          have hir : i - (points left).length < (points right).length := by
            simp only [List.length_append] at hi
            omega
          have hroot : right.poly.toPoly.eval (points right)[i - (points left).length] = 0 := by
            rw [hPr]
            exact eval_prod_X_sub_C_of_mem (List.getElem_mem hir)
          have hx : (points left ++ points right)[i] =
              (points right)[i - (points left).length] :=
            List.getElem_append_right hle
          rw [hx, hR.2 _ hir, hroot]
          have hidx : leafCount left + (i - (points left).length) = i := by omega
          simp only [hPl, eval_prod_X_sub_C,
            List.eraseIdx_append_of_length_le hle, List.map_append, List.prod_append,
            List.getElem_drop, hidx]
          ring

end Correctness

end SubproductTree

/-- On pairwise distinct nodes, subproduct-tree interpolation is Lagrange interpolation. -/
theorem interpolateSubproduct_eq_interpolateArrays [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) (D : ModContext R) (xs ys : Array R) (hxs : xs.toList.Nodup) :
    interpolateSubproduct M D xs ys = CLagrange.interpolateArrays xs ys := by
  have hinj : Set.InjOn (CLagrange.arrayNode xs) ↑(Finset.univ : Finset (Fin xs.size)) := by
    intro i _ j _ hij
    refine Fin.ext ((List.Nodup.getElem_inj_iff hxs (hi := by simp) (hj := by simp)).mp ?_)
    rw [Array.getElem_toList, Array.getElem_toList]
    exact hij
  apply toPoly_injective
  rw [CLagrange.interpolateArrays, CLagrange.cinterpolate_eq_interpolate]
  unfold interpolateSubproduct
  cases hbuild : SubproductTree.buildArray M xs with
  | none =>
      have hsize : xs.size = 0 := by
        by_contra hne
        obtain ⟨tree, htree⟩ := SubproductTree.buildList_exists_of_nonempty M
          (xs := xs.toList) (by simp; omega)
        simp [SubproductTree.buildArray, htree] at hbuild
      have hempty : (Finset.univ : Finset (Fin xs.size)) = ∅ := by
        rw [Finset.univ_eq_empty_iff, hsize]
        infer_instance
      simp [hempty, toPoly_zero]
  | some tree =>
      have hpoints := (SubproductTree.buildArray_valid_points M hbuild).2
      have hexact := SubproductTree.exact_buildArray M hbuild
      set ys' := List.ofFn fun i : Fin xs.size => ys.getD i 0
      have hlen : ys'.length = (SubproductTree.points tree).length := by
        simp [ys', hpoints]
      let ds := SubproductTree.evalList D (derivative tree.poly) tree
      have hds : ds = xs.toList.map (derivative tree.poly).eval := by
        dsimp only [ds]
        rw [SubproductTree.evalList_eq_map_eval D _ tree
          (SubproductTree.buildArray_valid_points M hbuild).1, hpoints]
      have hne (x : R) (hx : x ∈ ds) : x ≠ 0 := by
        rw [hds] at hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
        rw [eval_toPoly, derivative_toPoly,
          SubproductTree.toPoly_poly_of_exact hexact, hpoints,
          SubproductTree.eval_derivative_prod_X_sub_C]
        refine List.prod_ne_zero ?_
        simp only [List.mem_map, not_exists, not_and]
        intro q hq hzero
        obtain ⟨k, hk, hkj, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hq
        exact hkj ((List.Nodup.getElem_inj_iff hxs).mp (sub_eq_zero.mp hzero).symm)
      have hweights : ys'.zipWith (· * ·) (CompPoly.List.batchInv ds) =
          List.ofFn (fun i : Fin xs.size => ys.getD i 0 /
            (derivative tree.poly).eval xs[i]) := by
        rw [CompPoly.List.batchInv_eq ds hne, hds]
        apply List.ext_getElem
        · simp only [List.length_zipWith, List.length_map, List.length_ofFn, ys',
            Array.length_toList, Nat.min_self]
        · intro i hi hi'
          simp only [List.getElem_zipWith, List.getElem_map, ys', List.getElem_ofFn,
            Array.getElem_toList, div_eq_mul_inv]
          rfl
      change (SubproductTree.interpolateWeights M tree
        (ys'.zipWith (· * ·) (CompPoly.List.batchInv ds))).toPoly = _
      rw [show SubproductTree.interpolateWeights M tree
          (ys'.zipWith (· * ·) (CompPoly.List.batchInv ds)) =
          SubproductTree.interpolateWeights M tree
            (List.ofFn fun i : Fin xs.size => ys.getD i 0 /
              (derivative tree.poly).eval xs[i]) by rw [hweights]]
      have hspec := SubproductTree.interpolateWeights_spec M tree hexact
        (List.ofFn fun i : Fin xs.size => ys.getD i 0 /
          (derivative tree.poly).eval xs[i]) (by simp only [List.length_ofFn, hpoints,
            Array.length_toList])
      simp only [hpoints] at hspec
      refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := Finset.univ)
        (v := CLagrange.arrayNode xs) hinj ?_ ?_ ?_
      · simpa using hspec.1
      · exact Lagrange.degree_interpolate_lt _ hinj
      · intro i _
        rw [Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)]
        have hi : i.1 < xs.toList.length := by simp
        have hnode : CLagrange.arrayNode xs i = xs.toList[i.1] := by
          simp [CLagrange.arrayNode]
        have hderiv : (derivative tree.poly).toPoly.eval xs.toList[i.1] =
            ((xs.toList.eraseIdx i.1).map fun q => xs.toList[i.1] - q).prod := by
          rw [derivative_toPoly, SubproductTree.toPoly_poly_of_exact hexact, hpoints]
          exact SubproductTree.eval_derivative_prod_X_sub_C _ i.1 hi
        have hne : ((xs.toList.eraseIdx i.1).map fun q => xs.toList[i.1] - q).prod ≠ 0 := by
          refine List.prod_ne_zero ?_
          simp only [List.mem_map, not_exists, not_and]
          intro q hq hzero
          obtain ⟨j, hj, hji, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hq
          exact hji ((List.Nodup.getElem_inj_iff hxs).mp (sub_eq_zero.mp hzero).symm)
        rw [hnode, hspec.2 i.1 hi]
        simp only [List.getElem_ofFn, ← eval_toPoly, Array.getElem_toList] at *
        change ys.getD i.val 0 / (derivative tree.poly).eval xs[i.val] *
          ((xs.toList.eraseIdx i.val).map fun q ↦ xs[i.val] - q).prod = _
        rw [hderiv, div_mul_cancel₀ _ hne]
        rfl

end CPolynomial
end CompPoly
