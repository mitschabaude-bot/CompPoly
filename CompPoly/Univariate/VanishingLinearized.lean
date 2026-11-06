/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import all CompPoly.Univariate.Basic
public import CompPoly.Univariate.ReedSolomon.GaoTree
public import CompPoly.Univariate.SparseMul

/-! # Certified vanishing polynomials from a binary subspace chain -/

@[expose] public section

namespace CompPoly.CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Evaluate a subspace chain starting at `X - offset`. -/
def vanishingChainEval {F : Type*} [Mul F] [Add F] [Sub F] (cs : List F) (offset x : F) : F :=
  cs.foldl (fun a c ↦ a * (a + c)) (x - offset)

/-- Construct the polynomial represented by a subspace chain. -/
def vanishingChainPolynomial (M : MulContext F) (cs : List F) (offset : F) : CPolynomial F :=
  cs.foldl (fun p c ↦ M.mul p (p + C c)) (linearFactor offset)

/-- Infer the successive subspace constants from coordinate-basis nodes. -/
def vanishingChainConstants {F : Type*} [Zero F] [Mul F] [Add F] [Sub F]
    (xs : Array F) (m : Nat) : List F :=
  (List.range m).foldl (fun cs i ↦
    cs ++ [vanishingChainEval cs (xs.getD 0 0) (xs.getD (2 ^ i) 0)]) []

/-- Check the inferred chain on every node and use its polynomial when certified. -/
def vanishingPolynomialLinearized (M : MulContext F) (xs : Array F) : CPolynomial F :=
  letI : DecidableEq F := fun a b ↦ decidable_of_iff ((a == b) = true) beq_iff_eq
  let m := xs.size.log2
  let cs := vanishingChainConstants xs m
  let offset := xs.getD 0 0
  if xs.size = 2 ^ m ∧ xs.toList.Nodup ∧
      xs.all (fun x ↦ vanishingChainEval cs offset x == 0) then
    vanishingChainPolynomial M cs offset
  else (VanishingPolynomialContext.subproduct M).vanishingPolynomial xs

private theorem chainFold_eval (M : MulContext F) (cs : List F) (p : CPolynomial F) (x : F) :
    eval x (cs.foldl (fun p c ↦ M.mul p (p + C c)) p) =
      cs.foldl (fun a c ↦ a * (a + c)) (eval x p) := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    rw [M.mul_eq_mul, eval_mul, eval_add, eval_C]

private theorem chainFold_monic_degree (M : MulContext F) (cs : List F)
    (p : CPolynomial F) (d : Nat) (hd : 0 < d)
    (hp : p.toPoly.Monic) (hdeg : p.toPoly.natDegree = d) :
    (cs.foldl (fun p c ↦ M.mul p (p + C c)) p).toPoly.Monic ∧
      (cs.foldl (fun p c ↦ M.mul p (p + C c)) p).toPoly.natDegree = d * 2 ^ cs.length := by
  induction cs generalizing p d with
  | nil =>
    simpa only [List.foldl_nil, List.length_nil, pow_zero, Nat.mul_one] using And.intro hp hdeg
  | cons c cs ih =>
    have hpos : (Polynomial.C c).degree < p.toPoly.degree := by
      rw [Polynomial.degree_eq_natDegree hp.ne_zero, hdeg]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast hd)
    have hsum : (p.toPoly + Polynomial.C c).Monic := hp.add_of_left hpos
    have hn : (M.mul p (p + C c)).toPoly.natDegree = d * 2 := by
      rw [M.mul_eq_mul, toPoly_mul, toPoly_add, C_toPoly,
        Polynomial.natDegree_mul hp.ne_zero hsum.ne_zero, Polynomial.natDegree_add_C, hdeg]
      omega
    have hm : (M.mul p (p + C c)).toPoly.Monic := by
      rw [M.mul_eq_mul, toPoly_mul, toPoly_add, C_toPoly]
      exact hp.mul hsum
    have hrec := ih (M.mul p (p + C c)) (d * 2) (by omega) hm hn
    simpa only [List.foldl_cons, List.length_cons, pow_succ, Nat.mul_assoc,
      Nat.mul_comm (2 ^ cs.length) 2] using hrec

omit [BEq F] [LawfulBEq F] in
private theorem chainConstants_length (xs : Array F) (m : Nat) :
    (vanishingChainConstants xs m).length = m := by
  have h (is : List Nat) (cs : List F) :
      (is.foldl (fun cs i ↦ cs ++ [vanishingChainEval cs (xs.getD 0 0)
        (xs.getD (2 ^ i) 0)]) cs).length = cs.length + is.length := by
    induction is generalizing cs with
    | nil => simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons i is ih =>
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  simpa only [vanishingChainConstants, List.length_nil, Nat.zero_add, List.length_range] using
    h (List.range m) []

/-- The chain construction is the node vanishing polynomial on every input. -/
theorem vanishingPolynomialLinearized_eq (M : MulContext F) (xs : Array F) :
    vanishingPolynomialLinearized M xs = vanishingPolynomialArray xs := by
  let : DecidableEq F := fun a b ↦ decidable_of_iff ((a == b) = true) beq_iff_eq
  unfold vanishingPolynomialLinearized
  dsimp only
  split
  · rename_i h
    let cs := vanishingChainConstants xs xs.size.log2
    let offset := xs.getD 0 0
    let D : ReedSolomon.Domain F := ⟨xs, h.2.1⟩
    have hlin : (linearFactor offset).toPoly = Polynomial.X - Polynomial.C offset := by
      simp only [linearFactor, toPoly_add, C_toPoly, X_toPoly, Polynomial.C_neg]
      ring
    have hspec := chainFold_monic_degree M cs (linearFactor offset) 1 (by decide)
      (hlin ▸ Polynomial.monic_X_sub_C offset)
      (by rw [hlin]; exact Polynomial.natDegree_X_sub_C offset)
    change (vanishingChainPolynomial M cs offset).toPoly.Monic ∧
      (vanishingChainPolynomial M cs offset).toPoly.natDegree = 1 * 2 ^ cs.length at hspec
    have hdeg : (vanishingChainPolynomial M cs offset).toPoly.natDegree = xs.size := by
      rw [hspec.2, Nat.one_mul, chainConstants_length, ← h.1]
    have hroot (i : Fin xs.size) :
        (vanishingChainPolynomial M cs offset).toPoly.eval xs[i] = 0 := by
      rw [← eval_toPoly, vanishingChainPolynomial, chainFold_eval]
      have heval : eval xs[i] (linearFactor offset) = xs[i] - offset := by
        rw [eval_toPoly, hlin, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [heval]
      exact eq_of_beq (Array.all_eq_true.mp h.2.2 i.val i.isLt)
    apply toPoly_injective
    rw [← ReedSolomon.Gao.nodalPoly_eq_vanishing D]
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    · rw [ReedSolomon.Gao.toPoly_nodalPoly]
      exact Polynomial.monic_prod_of_monic _ _ (fun _ _ ↦ Polynomial.monic_X_sub_C _)
    · exact hspec.1
    · rw [ReedSolomon.Gao.toPoly_nodalPoly]
      exact Polynomial.prod_X_sub_C_dvd _ _ D.node_injective.injOn _ (fun i _ ↦ hroot i)
    · rw [hdeg, ReedSolomon.Gao.natDegree_nodalPoly]
  · exact (VanishingPolynomialContext.subproduct M).correct xs

/-- Vanishing context using a certified binary-subspace chain when its nodes admit one. -/
def VanishingPolynomialContext.linearized (M : MulContext F) : VanishingPolynomialContext F where
  vanishingPolynomial := vanishingPolynomialLinearized M
  correct := vanishingPolynomialLinearized_eq M

end CompPoly.CPolynomial
