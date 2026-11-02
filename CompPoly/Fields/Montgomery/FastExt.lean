/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native32Ext4

/-!
# Fast extensions of 32-bit Montgomery fields

`FastExt p E` says that `E` is a field extension of `FastField p` with an executable carrier:
`E` has coordinates in the power basis of a monic modulus (`FastExt.params`), and its operations
are those of the spec field `Ext params`. The class is what coordinate-wise kernels over
extension elements, such as the coordinate planes of `Native32ExtPlanes.lean`, are generic over.

* `FastExt.toSpec` maps an element to the spec field element with its coordinates, and
  `FastExt.specEquiv` is the ring isomorphism.
* `FastExt.coord_mul` gives the coordinates of a product as the spec's product formula:
  coordinate `m` of `a * b` is `∑ᵢ ∑ⱼ aᵢ bⱼ [X^(i+j) mod f]ₘ`.

Instances: the quartic binomial extensions `Ext4 p` (here) and KoalaBear's quintic
`KoalaBear.Fast.Ext5`.
-/

@[expose] public section

namespace Montgomery.Native32

open CompPoly CompPoly.Extension

/-- A field extension `E` of `FastField p` given by its coordinates in the power basis of the
monic modulus `params.poly`, with the spec field's operations. -/
class FastExt (p : outParam ℕ) [Mont32Field p] (E : Type) extends Zero E, One E, Add E, Sub E,
    Neg E, Mul E, Inv E where
  [decEq : DecidableEq E]
  /-- The modulus of the spec field. -/
  params : ExtensionParams (FastField p)
  [card : Fact (Nat.card (FastField p) = params.q)]
  [irreducible : Fact (Irreducible params.poly)]
  /-- The coordinates, lowest first. -/
  coord : E → Fin params.d → FastField p
  /-- The element with the given coordinates. -/
  ofCoords : (Fin params.d → FastField p) → E
  coord_ofCoords (f : Fin params.d → FastField p) : coord (ofCoords f) = f
  coord_injective : Function.Injective coord
  coord_zero : coord 0 = 0
  ofFn_one : Ext.ofFn (coord 1) = 1
  coord_add (a b : E) : coord (a + b) = coord a + coord b
  coord_sub (a b : E) : coord (a - b) = coord a - coord b
  coord_neg (a : E) : coord (-a) = -coord a
  ofFn_mul (a b : E) : Ext.ofFn (coord (a * b)) = Ext.ofFn (coord a) * Ext.ofFn (coord b)
  ofFn_inv (a : E) : Ext.ofFn (coord a⁻¹) = (Ext.ofFn (coord a))⁻¹

namespace FastExt

attribute [instance_reducible] decEq
attribute [instance] card irreducible decEq

variable {p : ℕ} [Mont32Field p] {E : Type} [FastExt p E]

local notation "F" => FastField p

variable (p E) in
/-- The degree of the extension. -/
abbrev d : Nat := (params (p := p) (E := E)).d

variable (p E) in
/-- The spec field. -/
abbrev Spec : Type := Ext (params (p := p) (E := E))

/-- The spec field element with the same coordinates. -/
def toSpec (a : E) : Spec p E := Ext.ofFn (coord a)

@[simp] theorem coeff_toSpec (a : E) (i : Fin (d p E)) : Ext.coeff (toSpec a) i = coord a i :=
  Ext.coeff_ofFn _ _

theorem toSpec_injective : Function.Injective (toSpec (E := E)) := fun a b h ↦
  coord_injective (funext fun i ↦ by rw [← coeff_toSpec, h, coeff_toSpec])

theorem ext {a b : E} (h : ∀ i, coord a i = coord b i) : a = b :=
  coord_injective (funext h)

@[simp] theorem toSpec_ofCoords (f : Fin (d p E) → F) : toSpec (ofCoords (E := E) f) = Ext.ofFn f :=
  by rw [toSpec, coord_ofCoords]

@[simp] theorem toSpec_zero : toSpec (0 : E) = 0 := by
  ext i; rw [coeff_toSpec, coord_zero, Ext.coeff_zero]; rfl

@[simp] theorem toSpec_one : toSpec (1 : E) = 1 := ofFn_one

@[simp] theorem toSpec_add (a b : E) : toSpec (a + b) = toSpec a + toSpec b := by
  ext i; simp only [coeff_toSpec, coord_add, Ext.coeff_add, Pi.add_apply]

@[simp] theorem toSpec_sub (a b : E) : toSpec (a - b) = toSpec a - toSpec b := by
  ext i; simp only [coeff_toSpec, coord_sub, Ext.coeff_sub, Pi.sub_apply]

@[simp] theorem toSpec_neg (a : E) : toSpec (-a) = -toSpec a := by
  ext i; simp only [coeff_toSpec, coord_neg, Ext.coeff_neg, Pi.neg_apply]

@[simp] theorem toSpec_mul (a b : E) : toSpec (a * b) = toSpec a * toSpec b := ofFn_mul a b

@[simp] theorem toSpec_inv (a : E) : toSpec a⁻¹ = (toSpec a)⁻¹ := ofFn_inv a

/-- The element of a spec field element. -/
def ofSpec (x : Spec p E) : E := ofCoords (Ext.coeff x)

@[simp] theorem toSpec_ofSpec (x : Spec p E) : toSpec (ofSpec (E := E) x) = x := by
  rw [ofSpec, toSpec_ofCoords, Ext.ofFn_coeff]

@[simp] theorem ofSpec_toSpec (a : E) : ofSpec (toSpec a) = a :=
  toSpec_injective (by rw [toSpec_ofSpec])

variable (p E) in
/-- The fast and spec extensions are isomorphic rings. -/
def specEquiv : E ≃+* Spec p E where
  toFun := toSpec
  invFun := ofSpec
  left_inv := ofSpec_toSpec
  right_inv := toSpec_ofSpec
  map_mul' := toSpec_mul
  map_add' := toSpec_add

@[simp] theorem specEquiv_apply (a : E) : specEquiv p E a = toSpec a := rfl

/-- A base-field element. -/
def ofBase (x : F) : E := ofCoords fun i ↦ if (i : ℕ) = 0 then x else 0

@[simp] theorem toSpec_ofBase (x : F) : toSpec (ofBase (E := E) x) = Ext.ofBase x := by
  ext i; rw [ofBase, toSpec_ofCoords, Ext.coeff_ofFn, Ext.coeff_ofBase]

/-- The generator `X`. -/
def gen : E := ofCoords fun i ↦ if (i : ℕ) = 1 then 1 else 0

@[simp] theorem toSpec_gen : toSpec (gen : E) = Ext.gen := by
  rw [gen, toSpec_ofCoords]; rfl

/-- **Coordinates of products**: the spec's product formula. -/
theorem coord_mul (a b : E) (m : Fin (d p E)) :
    coord (a * b) m = ∑ i : Fin (d p E), ∑ j : Fin (d p E),
      coord a i * coord b j * Ext.coeff (Ext.monomialMod ((i : ℕ) + (j : ℕ)) :
        Spec p E) m := by
  rw [← coeff_toSpec, toSpec_mul]
  show Ext.coeff (Ext.mul _ _) m = _
  simp only [Ext.mul, Ext.coeff_ofFn, coeff_toSpec]

theorem mul_comm (a b : E) : a * b = b * a :=
  toSpec_injective (by rw [toSpec_mul, toSpec_mul, _root_.mul_comm])

theorem mul_assoc (a b c : E) : a * b * c = a * (b * c) :=
  toSpec_injective (by simp only [toSpec_mul, _root_.mul_assoc])

end FastExt

/-! ### The quartic binomial extensions -/

namespace Ext4

variable {p : ℕ} [Mont32Field p] [Binomial4 p]

/-- The quartic binomial extension `FastField p [X] / (X^4 - W)`. Inlined, so that code
specialized to it runs the extension's arithmetic directly. -/
@[inline] instance instFastExt : FastExt p (Ext4 p) where
  params := P p
  coord a i := coord a i
  ofCoords f := ⟨f ⟨0, by change 0 < 4; omega⟩, f ⟨1, by change 1 < 4; omega⟩,
    f ⟨2, by change 2 < 4; omega⟩, f ⟨3, by change 3 < 4; omega⟩⟩
  coord_ofCoords f := by
    funext ⟨i, hi⟩
    have hi : i < 4 := hi
    interval_cases i <;> rfl
  coord_injective a b h := by
    have e (k : Nat) (hk : k < 4) : coord a k = coord b k := congrFun h ⟨k, hk⟩
    exact ext' (e 0 (by decide)) (e 1 (by decide)) (e 2 (by decide)) (e 3 (by decide))
  coord_zero := by
    funext ⟨i, hi⟩
    have hi : i < 4 := hi
    interval_cases i <;> rfl
  ofFn_one := toSpec_one
  coord_add a b := by
    funext ⟨i, hi⟩
    have hi : i < 4 := hi
    interval_cases i <;> rfl
  coord_sub a b := by
    funext ⟨i, hi⟩
    have hi : i < 4 := hi
    interval_cases i <;> rfl
  coord_neg a := by
    funext ⟨i, hi⟩
    have hi : i < 4 := hi
    interval_cases i <;> rfl
  ofFn_mul := toSpec_mul
  ofFn_inv := toSpec_inv

theorem toSpec_fastExt (a : Ext4 p) : FastExt.toSpec a = toSpec a := rfl

@[simp] theorem d_fastExt : FastExt.d p (Ext4 p) = 4 := rfl

end Ext4

end Montgomery.Native32
