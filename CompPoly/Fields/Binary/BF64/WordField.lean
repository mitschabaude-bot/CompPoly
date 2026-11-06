/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.MaskedOpsProofs
public import CompPoly.Fields.Binary.BF64.WordExt3Frobenius
public import Mathlib.Algebra.Field.TransferInstance

/-! # Executable fields on the polynomial-basis word carriers -/

@[expose] public section

namespace BF64

/-- Binary exponentiation parameterized by the executable identity and product. -/
def wordPow {A : Type*} (one : A) (mul : A → A → A) (a : A) (n : Nat) : A :=
  if h : n = 0 then one else
    let b := wordPow one mul a (n / 2)
    if n % 2 = 0 then mul b b else mul (mul b b) a
termination_by n

/-- Binary powers commute with a multiplication-preserving injection. -/
theorem map_wordPow {A F : Type*} [Monoid F]
    (f : A → F) (_hf : Function.Injective f) (one : A) (mul : A → A → A)
    (h1 : f one = 1) (hm : ∀ a b, f (mul a b) = f a * f b) (a : A) (n : Nat) :
    f (wordPow one mul a n) = f a ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [wordPow]
    split
    · rename_i hn
      simp only [h1, hn, pow_zero]
    · rename_i hn
      have hi := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      split
      · rename_i he
        rw [hm, hi, ← pow_add]
        congr 1
        omega
      · rename_i he
        rw [hm, hm, hi, ← pow_add, ← pow_succ]
        congr 1
        omega

/-- Pull back field laws while retaining explicitly supplied executable operations. -/
abbrev fieldOfWordOps {A F : Type*} [Field F] (e : A ≃ F)
    (add mul : A → A → A) (neg : A → A) (sub : A → A → A) (inv : A → A)
    (ha : ∀ a b, e (add a b) = e a + e b)
    (hm : ∀ a b, e (mul a b) = e a * e b)
    (hn : ∀ a, e (neg a) = -e a)
    (hs : ∀ a b, e (sub a b) = e a - e b)
    (hi : ∀ a, e (inv a) = (e a)⁻¹) : Field A := by
  letI : Zero A := ⟨e.symm 0⟩
  letI : One A := ⟨e.symm 1⟩
  letI : Add A := ⟨add⟩
  letI : Mul A := ⟨mul⟩
  letI : Neg A := ⟨neg⟩
  letI : Sub A := ⟨sub⟩
  letI : NatCast A := ⟨fun n ↦ e.symm n⟩
  letI : IntCast A := ⟨fun n ↦ e.symm n⟩
  letI : SMul Nat A := e.smul Nat
  letI : SMul Int A := e.smul Int
  letI : Pow A Nat := ⟨wordPow (e.symm 1) mul⟩
  have h0 : e (0 : A) = 0 := e.apply_symm_apply _
  have h1 : e (1 : A) = 1 := e.apply_symm_apply _
  letI : CommRing A := e.injective.commRing e h0 h1 ha hm hn hs
    (fun _ _ ↦ e.apply_symm_apply _) (fun _ _ ↦ e.apply_symm_apply _)
    (map_wordPow e e.injective _ mul h1 hm)
    (fun _ ↦ e.apply_symm_apply _) (fun _ ↦ e.apply_symm_apply _)
  letI : Inv A := ⟨inv⟩
  letI : Div A := ⟨fun a b ↦ mul a (inv b)⟩
  exact {
    toCommRing := inferInstance
    inv := inv
    div := fun a b ↦ mul a (inv b)
    div_eq_mul_inv := fun _ _ ↦ rfl
    exists_pair_ne := ⟨e.symm 0, e.symm 1, fun h ↦ (zero_ne_one : (0 : F) ≠ 1) (by
      simpa only [e.apply_symm_apply] using congrArg e h)⟩
    mul_inv_cancel := fun a h ↦ e.injective (by
      change e (mul a (inv a)) = e (e.symm 1)
      rw [hm, hi, e.apply_symm_apply]
      exact mul_inv_cancel₀ (fun hz ↦ h (e.injective (hz.trans h0.symm))))
    inv_zero := e.injective (by rw [hi, h0, inv_zero])
    qsmul := (Rat.castRec · * ·)
    nnqsmul := (NNRat.castRec · * ·) }

namespace Word

/-- The polynomial-coordinate bijection to the specification field. -/
def equivField : Word ≃ BF64 :=
  ⟨toField, ofField, ofField_toField, toField_ofField⟩

instance : Field Word := fieldOfWordOps equivField add mulMasked id add invMasked
  toField_add toField_mulMasked (fun _ ↦ rfl)
  (fun _ _ ↦ toField_add _ _) toField_invMasked

/-- The word carrier and specification have the same field operations. -/
def ringEquiv : Word ≃+* BF64 where
  toEquiv := equivField
  map_add' := toField_add
  map_mul' := toField_mulMasked

instance : LawfulBEq Word where
  eq_of_beq {a b} h := by cases a; cases b; congr 1; exact eq_of_beq h
  rfl {a} := by change (a.val == a.val) = true; exact BEq.rfl

end Word

namespace WordExt3

/-- The ordered three-coordinate bijection to the specification extension. -/
def equivField : WordExt3 ≃ Ext3 :=
  ⟨toField, ofField, ofField_toField, toField_ofField⟩

private theorem toField_one : toField (ofField 1) = 1 := toField_ofField _

/-- Binary exponentiation on the six-product extension kernel. -/
def powWord (a : WordExt3) (n : Nat) : WordExt3 := wordPow (ofField 1) mul a n

/-- Binary word powers agree with extension powers. -/
theorem toField_powWord (a : WordExt3) (n : Nat) :
    toField (powWord a n) = toField a ^ n :=
  map_wordPow toField toField_injective _ mul toField_one toField_mul a n

/-- Fermat inversion, including zero, using only extension word products. -/
def invWord (a : WordExt3) : WordExt3 := powWord a (2 ^ 192 - 2)

/-- The extension word inverse agrees with the specification inverse. -/
theorem toField_invWord (a : WordExt3) : toField (invWord a) = (toField a)⁻¹ := by
  rw [invWord, toField_powWord]
  exact (CompPoly.Extension.Ext.inv_def (toField a)).symm

/-- The specification extension has characteristic two. -/
theorem neg_toField (a : WordExt3) : -(toField a) = toField a := by
  apply CompPoly.Extension.Ext.ext
  intro i
  rw [CompPoly.Extension.Ext.coeff_neg]
  rfl

instance : Field WordExt3 := fieldOfWordOps equivField add mul id add invWord
  toField_add toField_mul (fun a ↦ (neg_toField a).symm)
  (fun a b ↦ by
    change toField (add a b) = toField a - toField b
    rw [toField_add, sub_eq_add_neg, neg_toField]) toField_invWord

/-- The three-word carrier and specification extension are isomorphic as fields. -/
def ringEquiv : WordExt3 ≃+* Ext3 where
  toEquiv := equivField
  map_add' := toField_add
  map_mul' := toField_mul

deriving instance ReflBEq, LawfulBEq for WordExt3

end WordExt3
end BF64
