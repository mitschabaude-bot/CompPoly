/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Scratch
import all Init.Data.Fin.Fold
/-! # Certified traversal with machine-sized loop counters -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace AdditiveNTT.Bitsliced

/-- The successor of an in-range loop counter does not wrap. -/
theorem next_toNat (n i : USize) (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  rw [USize.lt_iff_toNat_lt] at h
  have h1 : (1 : USize).toNat = 1 :=
    USize.toNat_ofNat_of_lt (lt_of_lt_of_le (by decide) USize.le_size)
  rw [USize.toNat_add, h1, Nat.mod_eq_of_lt]
  have := n.toNat_lt_size
  change n.toNat < 2 ^ System.Platform.numBits at this
  omega

/-- Tail-recursive traversal of a machine interval. -/
@[specialize] def foldAux (n : USize) (f : (i : USize) → i < n → α → α)
    (a : α) (i : USize) : α :=
  if h : i < n then foldAux n f (f i h a) (i + 1) else a
termination_by n.toNat - i.toNat
decreasing_by
  rw [next_toNat n i h]
  have := USize.lt_iff_toNat_lt.mp h
  omega

/-- Visit every machine index once, in ascending order. -/
@[specialize] def fold (n : USize) (f : (i : USize) → i < n → α → α) (a : α) : α :=
  foldAux n f a 0

/-- The machine traversal is the existing finite left fold. -/
theorem foldAux_eq (n : USize) (f : (i : USize) → i < n → α → α) (a : α) (i : USize) :
    foldAux n f a i = Fin.foldl.loop n.toNat (fun a j =>
      f (USize.ofNat j.val) (by
        rw [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt' (lt_trans j.isLt n.toNat_lt_size)]
        exact j.isLt) a) a i.toNat := by
  rw [foldAux, Fin.foldl.loop]
  by_cases h : i < n
  · have ht : i.toNat < n.toNat := USize.lt_iff_toNat_lt.mp h
    rw [dite_eq_left h, dite_eq_left ht, foldAux_eq n f (f i h a) (i + 1), next_toNat n i h]
    simp only [USize.ofNat_toNat]
  · have ht : ¬i.toNat < n.toNat := fun ht => h (USize.lt_iff_toNat_lt.mpr ht)
    rw [dite_eq_right h, dite_eq_right ht]
termination_by n.toNat - i.toNat
decreasing_by
  rw [next_toNat n i h]
  have := USize.lt_iff_toNat_lt.mp h
  omega

/-- Starting the traversal at zero agrees with the finite specification. -/
theorem fold_eq (n : USize) (f : (i : USize) → i < n → α → α) (a : α) :
    fold n f a = Fin.foldl n.toNat (fun a j =>
      f (USize.ofNat j.val) (by
        rw [USize.lt_iff_toNat_lt, USize.toNat_ofNat_of_lt' (lt_trans j.isLt n.toNat_lt_size)]
        exact j.isLt) a) a := by
  rw [fold, foldAux_eq, Fin.foldl_eq_foldlTR]
  rfl

end AdditiveNTT.Bitsliced
