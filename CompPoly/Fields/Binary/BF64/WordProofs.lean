/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Word

/-! # Refinement of scalar BF64 words to the quotient field -/

@[expose] public section

open BF64 BinaryField
set_option maxRecDepth 10000

namespace BF64.Word
set_option maxHeartbeats 2000000
private theorem poly_inj {w : Nat} {a b : BitVec w} (h : toPoly a = toPoly b) : a = b := by
  have hz : toPoly (a ^^^ b) = 0 := by rw [toPoly_xor, h, ZMod2Poly.add_self_cancel]
  have hb : a ^^^ b = 0 := by
    by_contra hn
    exact (toPoly_ne_zero_iff_ne_zero _).mpr hn hz
  exact BitVec.xor_eq_zero_iff.mp hb
/-- Full carry-less multiplication is commutative. -/
theorem cmul_comm (a b : BitVec 64) : carryLessMul (w := 128) a b = carryLessMul b a := by
  apply poly_inj
  rw [toPoly_carryLessMul a b (by omega), toPoly_carryLessMul b a (by omega), mul_comm]
/-- Multiplication by the BF64 reduction tail uses four shifted copies. -/
theorem cmul_tail (a : BitVec 64) : carryLessMul (w := 128) reductionConstant a =
    ((zeroExtendTo a ^^^ (zeroExtendTo a <<< 1)) ^^^ (zeroExtendTo a <<< 3)) ^^^
      (zeroExtendTo a <<< 4) := by
  unfold carryLessMul reductionConstant
  simp only [Fin.foldl_succ_last, Fin.foldl_zero, Fin.val_castSucc, Fin.val_last]
  norm_num [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit_eq_decide_div_mod_eq, BitVec.zero_xor]
  all_goals exact BitVec.zero_xor
private theorem cmul_two (a : BitVec 64) : carryLessMul (w := 128) (2#64) a =
    zeroExtendTo a <<< 1 := by
  unfold carryLessMul
  simp only [Fin.foldl_succ_last, Fin.foldl_zero, Fin.val_castSucc, Fin.val_last]
  norm_num [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit_eq_decide_div_mod_eq, BitVec.zero_xor]
  all_goals exact BitVec.zero_xor

private theorem top_bit (a : BitVec 64) : a >>> 63 = if a.getLsbD 63 then 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i = 0
  · subst i
    cases hb : a.getLsbD 63 <;> have hb' : a[63] = _ := hb <;> simp [hb']
  · have hge : 64 ≤ 63 + i := by omega
    cases hb : a.getLsbD 63 <;> simp [BitVec.getLsbD_of_ge _ _ hge, BitVec.getLsbD_ofNat,
      Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))]
private theorem xtime_eq (a : BitVec 64) : (a <<< 1) ^^^ ((0 - (a >>> 63)) &&& 0x1b) =
    reduce (carryLessMul (w := 128) (2#64) a) := by
  rw [cmul_two]
  unfold reduce foldStep
  rw [cmul_comm, cmul_tail, cmul_comm, cmul_tail]
  rw [top_bit]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> cases h : a.getLsbD 63 <;>
    have h' : a[63] = _ := h <;>
    simp [highHalf, lowHalf, zeroExtendTo, BitVec.getLsbD_of_ge, h']

lemma toField_xtime (a : UInt64) :
    toField ⟨xtime a⟩ = toField ⟨2⟩ * toField ⟨a⟩ := by
  apply BF64.ext
  change (xtime a).toBitVec = _
  change (a.toBitVec <<< 1) ^^^ ((0 - (a.toBitVec >>> 63)) &&& 0x1b) =
    reduce (carryLessMul (w := 128) (2#64) a.toBitVec)
  exact xtime_eq a.toBitVec

lemma mask_bit (a b : UInt64) :
    (((0 : UInt64) - (b &&& 1)) &&& a).toBitVec =
      if b.toBitVec.getLsbD 0 then a.toBitVec else 0 := by
  change ((0#64 - (b.toBitVec &&& 1#64)) &&& a.toBitVec) = _
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : b.toBitVec.getLsbD 0 <;>
    simp [BitVec.ofBool, BitVec.neg_one_eq_allOnes, BitVec.sub_eq_add_neg]
  all_goals exact BitVec.allOnes_and

lemma split_bit (b : UInt64) :
    toField ⟨b⟩ = toField ⟨2⟩ * toField ⟨b >>> 1⟩ +
      if b.toBitVec.getLsbD 0 then 1 else 0 := by
  rw [← toField_xtime]
  apply BF64.ext
  change b.toBitVec = (xtime (b >>> 1)).toBitVec ^^^ _
  change b.toBitVec = ((b.toBitVec >>> 1) <<< 1) ^^^
    ((0 - ((b.toBitVec >>> 1) >>> 63)) &&& 0x1b) ^^^
    (if b.toBitVec.getLsbD 0 then (1 : BF64) else 0).toBitVec
  rw [← BitVec.shiftRight_add, show 1 + 63 = 64 from rfl,
    show b.toBitVec >>> 64 = 0 from BitVec.ushiftRight_eq_zero (by decide)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i = 0
  · subst i
    cases hb : b.toBitVec.getLsbD 0 <;> have hb' : b.toBitVec[0] = _ := hb <;>
      simp
  · have hs : 1 + (i - 1) = i := by omega
    cases hb : b.toBitVec.getLsbD 0 <;>
      simp [hs, h, hi]

lemma mulLoop_agrees (n : Nat) (a b acc : UInt64) (hb : b.toNat < 2 ^ n) :
    toField ⟨mulLoop n a b acc⟩ = toField ⟨acc⟩ + toField ⟨a⟩ * toField ⟨b⟩ := by
  induction n generalizing a b acc with
  | zero =>
    have hz : b = 0 := UInt64.toNat_inj.mp (by
      change b.toNat = 0
      simp only [pow_zero] at hb
      omega)
    subst b
    simp only [mulLoop]
    change _ = _ + _ * 0
    rw [mul_zero, add_zero]
  | succ n ih =>
    have hs : (b >>> 1).toNat < 2 ^ n := by
      change b.toNat / 2 < 2 ^ n
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa only [pow_succ] using hb
    rw [mulLoop, ih _ _ _ hs]
    have hm : toField ⟨acc ^^^ (((0 : UInt64) - (b &&& 1)) &&& a)⟩ =
        toField ⟨acc⟩ + if b.toBitVec.getLsbD 0 then toField ⟨a⟩ else 0 := by
      apply BF64.ext
      change (acc ^^^ _).toBitVec = _
      simp only [UInt64.toBitVec_xor, mask_bit]
      cases b.toBitVec.getLsbD 0 <;> rfl
    rw [hm, toField_xtime, split_bit b]
    cases b.toBitVec.getLsbD 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

lemma mulLoopFast_eq (n : UInt64) (a b acc : UInt64) :
    mulLoopFast n a b acc = mulLoop n.toNat a b acc := by
  induction hk : n.toNat generalizing n a b acc with
  | zero =>
    have hz : n = 0 := UInt64.toNat_inj.mp hk
    subst n
    rw [mulLoopFast]
    rfl
  | succ k ih =>
    have hn : n ≠ 0 := by intro hz; subst n; contradiction
    have hle : (1 : UInt64) ≤ n := by change 1 ≤ n.toNat; omega
    have hsub : (n - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ hle]
      change n.toNat - 1 = k
      omega
    rw [mulLoopFast, dite_eq_right hn, ih _ _ _ _ hsub]
    rfl

@[simp] theorem toField_mul (a b : Word) :
    toField (mul a b) = toField a * toField b := by
  simpa only [mul, mulLoopFast_eq, show (64 : UInt64).toNat = 64 from rfl,
    show toField ⟨0⟩ = (0 : BF64) from rfl, zero_add] using
    mulLoop_agrees 64 a.val b.val 0 b.val.toBitVec.isLt
/-- Word squaring agrees with specification multiplication. -/
@[simp] theorem toField_square (a : Word) : toField (square a) = toField a * toField a :=
  toField_mul a a

/-- Repeated word squaring is the specification Frobenius. -/
@[simp] theorem toField_frobenius (a : Word) (n : Nat) :
    toField (frobenius a n) = BF64.powTwoPow (toField a) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [frobenius, BF64.powTwoPow, ih, toField_square]

private theorem powTwoPow_zero (n : Nat) : BF64.powTwoPow 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [BF64.powTwoPow, mul_zero] using ih

/-- The scalar Itoh–Tsujii chain agrees with field inversion, including zero. -/
@[simp] theorem toField_inv (a : Word) : toField (inv a) = (toField a)⁻¹ := by
  rw [BF64.inv_def, BF64.invItohTsujii]
  by_cases h : toField a = 0
  · simp only [h, ite_true, inv, toField_square, toField_mul, toField_frobenius,
      powTwoPow_zero, mul_zero]
  · simp only [h, ite_false, inv, toField_square, toField_mul, toField_frobenius]

/-- The word codec is byte-for-byte the polynomial-basis specification codec. -/
@[simp] theorem toBytes_toField (a : Word) :
    CompPoly.ByteCodec.toBytes a = CompPoly.ByteCodec.toBytes a.toField := rfl

end BF64.Word
