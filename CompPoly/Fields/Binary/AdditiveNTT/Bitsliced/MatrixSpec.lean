/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Transpose
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.FlatBasis
/-! # Binary linear-map semantics for shared-scalar plane multiplication -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace AdditiveNTT.Bitsliced
open BF64

/-- A polynomial bit, as an additive functional into the binary prime field. -/
def coordinate (i : Fin 64) : BF64 →+ ZMod 2 where
  toFun a := if a.toBitVec.getLsbD i.val then 1 else 0
  map_zero' := by simp only [BF64.toBitVec_zero, BitVec.getLsbD_zero, Bool.false_eq_true, ite_false]
  map_add' a b := by
    simp only [BF64.add_def, BF64.toBitVec_ofBitVec, BitVec.getLsbD_xor]
    have hf (x y : Bool) : (if x ^^ y then (1 : ZMod 2) else 0) =
        (if x then 1 else 0) + (if y then 1 else 0) := by
      cases x <;> cases y <;> decide
    exact hf _ _

/-- A binary dot product, viewed in the polynomial-basis field. -/
def dotSpec (m : UInt64) (a : Block) : BF64 :=
  ∑ j : Fin 64, if m.toBitVec.getLsb j then Word.toField ⟨a.get j⟩ else 0

/-- Select a lane's raw word from the bit-plane representation. -/
def lane (a : Block) (i : Fin 64) : Word := ⟨(transpose a).get i⟩

/-- Taking a bit commutes with a finite binary linear combination. -/
theorem coordinate_dotSpec (m : UInt64) (a : Block) (i : Fin 64) :
    coordinate i (dotSpec m a) =
      ∑ j : Fin 64, if m.toBitVec.getLsb j then coordinate i (Word.toField ⟨a.get j⟩) else 0 := by
  simp only [dotSpec, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp

/-- Binary coefficient tests determine a field word. -/
theorem coordinate_ext {a b : BF64} (h : ∀ i, coordinate i a = coordinate i b) : a = b := by
  apply BF64.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc := h ⟨i, hi⟩
  change (if a.toBitVec.getLsbD i then (1 : ZMod 2) else 0) =
    (if b.toBitVec.getLsbD i then 1 else 0) at hc
  cases ha : a.toBitVec.getLsbD i <;> cases hb : b.toBitVec.getLsbD i <;>
    simp only [ha, hb, Bool.false_eq_true, ite_false, ite_true] at hc ⊢
  all_goals contradiction

/-- The unrolled columns follow multiplication by successive powers of X. -/
theorem columns_get (t : UInt64) (j : Fin 64) :
    (columns t).get j = (Word.xtime^[j.val]) t := by
  fin_cases j <;> rfl

/-- Iterating the word shift agrees with a field power. -/
theorem xtime_iterate (n : Nat) (t : UInt64) :
    Word.toField ⟨(Word.xtime^[n]) t⟩ = Word.toField ⟨2⟩ ^ n * Word.toField ⟨t⟩ := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Word.toField_xtime, ih, pow_succ]
    ac_rfl

/-- No basis bit reduces before it reaches degree sixty-four. -/
theorem xtime_iterate_one (j : Fin 64) :
    (Word.xtime^[j.val]) 1 = (Packed.flatBasis j).val := by
  fin_cases j <;> decide

/-- Each matrix column is the scalar times its polynomial-basis vector. -/
theorem columns_toField (t : UInt64) (j : Fin 64) :
    Word.toField ⟨(columns t).get j⟩ = Word.toField ⟨t⟩ * (Packed.flatBasis j).toField := by
  rw [columns_get, xtime_iterate]
  have hb := xtime_iterate j.val 1
  rw [xtime_iterate_one] at hb
  change (Packed.flatBasis j).toField = Word.toField ⟨2⟩ ^ j.val * 1 at hb
  rw [mul_one] at hb
  rw [hb, mul_comm]

/-- Each binary matrix entry is the corresponding scalar-product coefficient. -/
theorem matrix_bit (t : UInt64) (i j : Fin 64) :
    bit (matrix t) i j = (Word.toField ⟨t⟩ * (Packed.flatBasis j).toField).toBitVec.getLsb i := by
  rw [matrix, bit_transpose]
  change (Word.toField ⟨(columns t).get j⟩).toBitVec.getLsb i = _
  rw [columns_toField]

/-- Transposition exchanges a lane coordinate with a plane coordinate. -/
theorem coordinate_lane (a : Block) (i j : Fin 64) :
    coordinate i (lane a j).toField = coordinate j (Word.toField ⟨a.get i⟩) := by
  exact congrArg (fun b => if b then (1 : ZMod 2) else 0) (bit_transpose a j i)

/-- The mathematical row-matrix application. -/
def applySpec (t : UInt64) (a : Block) : Block :=
  Block.ofFn fun i => (Word.ofField (dotSpec ((matrix t).get i) a)).val

/-- A specification output plane is its matrix row's binary dot product. -/
theorem applySpec_get (t : UInt64) (a : Block) (i : Fin 64) :
    Word.toField ⟨(applySpec t a).get i⟩ = dotSpec ((matrix t).get i) a := by
  simp only [applySpec, Block.get_ofFn]
  exact Word.toField_ofField _

/-- The binary matrix represents multiplication in every lane. -/
theorem lane_applySpec (t : UInt64) (a : Block) (j : Fin 64) :
    (lane (applySpec t a) j).toField = Word.toField ⟨t⟩ * (lane a j).toField := by
  apply coordinate_ext
  intro i
  rw [coordinate_lane, applySpec_get, coordinate_dotSpec]
  conv_rhs => rw [BF64.eq_sum_binaryBasisVector (lane a j).toField]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hm := matrix_bit t i k
  change ((matrix t).get i).toBitVec.getLsb k = _ at hm
  have ha := bit_transpose a j k
  change ((transpose a).get j).toBitVec.getLsb k = (a.get k).toBitVec.getLsb j at ha
  rw [hm]
  simp only [Packed.flatBasis_toField, mul_ite, mul_zero]
  split_ifs with hprod hinput
  all_goals simp only [coordinate, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lane,
    Word.toField, BF64.toBitVec_ofBitVec] at *
  all_goals
    have ha := bit_transpose a j k
    change ((transpose a).get j).toBitVec.getLsb k = (a.get k).toBitVec.getLsb j at ha
    simp_all only [BitVec.getLsb, BitVec.getLsbD, BF64.toBitVec_zero,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_testBit, Bool.false_eq_true, ite_false, ite_true]

end AdditiveNTT.Bitsliced
