/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.MaskedLemmas
public import CompPoly.Fields.Binary.BF64.WordProofs

/-! # Polynomial identities for masked-integer BF64 multiplication -/

public section

namespace BF64.Word
open BinaryField Polynomial MaskedLemmas
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

private theorem stripeShift (a : BitVec 64) (r : Nat) (_hr : r < 4) :
    a &&& ((0x11111111#64) <<< r) = ((a >>> r) &&& (0x11111111#64)) <<< r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h : r ≤ i
  · simp [hi, show ¬i < r by omega, show r + (i-r) = i by omega,
      Bool.and_comm]
  · simp [hi, show i < r by omega]

private theorem maskShift (a : BitVec 64) (d : Nat) (hd : d < 7) :
    (a <<< d) &&& ((0x1111111111111111#64) <<< (d % 4)) =
      (a &&& (0x1111111111111111#64)) <<< d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases d <;> interval_cases i <;> simp

private theorem productShift (a b : BitVec 64) (r s : Nat) :
    (a <<< r) * (b <<< s) = (a*b) <<< (r+s) := by
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  have ht : BitVec.twoPow 64 (r+s) = BitVec.twoPow 64 r * BitVec.twoPow 64 s := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_twoPow, BitVec.toNat_mul, Nat.pow_add,
      Nat.mul_mod, Nat.mod_mod]
  rw [ht]
  ac_rfl

private theorem stripeBound (a : BitVec 64) :
    (a &&& (0x11111111#64)).toNat < 2^29 := by
  rw [BitVec.toNat_and]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem narrowPoly (a : BitVec 64) (ha : a.toNat < 2^32) :
    toPoly (a.setWidth 32) = toPoly a := by
  have h : (a.setWidth 32).setWidth 64 = a :=
    BitVec.setWidth_setWidth_eq_self (by
      change a.toNat < (BitVec.twoPow 64 32).toNat
      simpa only [BitVec.toNat_twoPow_of_lt (by decide : 32 < 64)] using ha)
  have hp := toPoly_zeroExtendTo (a.setWidth 32) (w := 64) (by omega)
  change toPoly ((a.setWidth 32).setWidth 64) = _ at hp
  rw [h] at hp
  exact hp.symm

private theorem stripeProductBound (a b : BitVec 64) :
    (((a &&& 0x11111111#64) * (b &&& 0x11111111#64)) &&&
      0x1111111111111111#64).toNat < 2^58 := by
  rw [stripeBV]
  apply BF64.carryLessMul_lt (p := 29) (q := 29) (h := by omega)
  all_goals
    rw [BitVec.toNat_setWidth]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (stripeBound _)

private theorem stripeProductPoly (a b : BitVec 64) :
    toPoly (((a &&& 0x11111111#64) * (b &&& 0x11111111#64)) &&&
      0x1111111111111111#64) =
      toPoly (a &&& 0x11111111#64) * toPoly (b &&& 0x11111111#64) := by
  rw [stripeBV, toPoly_carryLessMul _ _ (by omega)]
  rw [narrowPoly _ (lt_trans (stripeBound _) (by decide)),
    narrowPoly _ (lt_trans (stripeBound _) (by decide))]

private theorem stripePairPoly (a b : BitVec 64) (r s : Nat) (hr : r < 4) (hs : s < 4) :
    toPoly (((a &&& ((0x11111111#64) <<< r)) *
        (b &&& ((0x11111111#64) <<< s))) &&&
        ((0x1111111111111111#64) <<< ((r+s) % 4))) =
      toPoly (a &&& ((0x11111111#64) <<< r)) *
        toPoly (b &&& ((0x11111111#64) <<< s)) := by
  rw [stripeShift a r hr, stripeShift b s hs, productShift,
    maskShift _ _ (by omega),
    toPoly_shiftLeft_no_overflow _ (stripeProductBound _ _) (by omega),
    stripeProductPoly,
    toPoly_shiftLeft_no_overflow _ (stripeBound _) (by omega),
    toPoly_shiftLeft_no_overflow _ (stripeBound _) (by omega), pow_add]
  ring

private theorem xorAnd (a b c : BitVec 64) :
    (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

private theorem stripeBound32 (a : BitVec 64) (r : Nat) (_hr : r < 4) :
    (a &&& ((0x11111111#64) <<< r)).toNat < 2^32 := by
  rw [BitVec.toNat_and]
  apply lt_of_le_of_lt Nat.and_le_right
  interval_cases r <;> decide

private theorem stripesPoly (a : BitVec 64) :
    toPoly (a.setWidth 32) = toPoly (a &&& 0x11111111#64) +
      toPoly (a &&& 0x22222222#64) + toPoly (a &&& 0x44444444#64) +
      toPoly (a &&& 0x88888888#64) := by
  have h : a.setWidth 32 = ((a &&& 0x11111111#64) ^^^ (a &&& 0x22222222#64) ^^^
      (a &&& 0x44444444#64) ^^^ (a &&& 0x88888888#64)).setWidth 32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp
  rw [h]
  simp only [BitVec.setWidth_xor, toPoly_xor]
  have h0 : (a &&& 0x11111111#64).toNat < 2^32 :=
    stripeBound32 a 0 (by decide)
  have h1 : (a &&& 0x22222222#64).toNat < 2^32 :=
    stripeBound32 a 1 (by decide)
  have h2 : (a &&& 0x44444444#64).toNat < 2^32 :=
    stripeBound32 a 2 (by decide)
  have h3 : (a &&& 0x88888888#64).toNat < 2^32 :=
    stripeBound32 a 3 (by decide)
  rw [narrowPoly _ h0, narrowPoly _ h1, narrowPoly _ h2, narrowPoly _ h3]

/-- The masked 32-bit kernel denotes the full polynomial product. -/
theorem clMul32_poly (a b : UInt64) :
    toPoly (clMul32 a b).toBitVec =
      toPoly (a.toBitVec.setWidth 32) * toPoly (b.toBitVec.setWidth 32) := by
  simp only [clMul32, UInt64.toBitVec_xor, UInt64.toBitVec_and,
    UInt64.toBitVec_mul, UInt64.toBitVec_ofNat, xorAnd, toPoly_xor]
  rw [stripesPoly, stripesPoly]
  have h00 :
      toPoly ((a.toBitVec &&& 0x11111111#64) *
        (b.toBitVec &&& 0x11111111#64) &&& 0x1111111111111111#64) =
      toPoly (a.toBitVec &&& 0x11111111#64) *
        toPoly (b.toBitVec &&& 0x11111111#64) :=
    stripePairPoly a.toBitVec b.toBitVec 0 0 (by decide) (by decide)
  have h01 :
      toPoly ((a.toBitVec &&& 0x11111111#64) *
        (b.toBitVec &&& 0x22222222#64) &&& 0x2222222222222222#64) =
      toPoly (a.toBitVec &&& 0x11111111#64) *
        toPoly (b.toBitVec &&& 0x22222222#64) :=
    stripePairPoly a.toBitVec b.toBitVec 0 1 (by decide) (by decide)
  have h02 :
      toPoly ((a.toBitVec &&& 0x11111111#64) *
        (b.toBitVec &&& 0x44444444#64) &&& 0x4444444444444444#64) =
      toPoly (a.toBitVec &&& 0x11111111#64) *
        toPoly (b.toBitVec &&& 0x44444444#64) :=
    stripePairPoly a.toBitVec b.toBitVec 0 2 (by decide) (by decide)
  have h03 :
      toPoly ((a.toBitVec &&& 0x11111111#64) *
        (b.toBitVec &&& 0x88888888#64) &&& 0x8888888888888888#64) =
      toPoly (a.toBitVec &&& 0x11111111#64) *
        toPoly (b.toBitVec &&& 0x88888888#64) :=
    stripePairPoly a.toBitVec b.toBitVec 0 3 (by decide) (by decide)
  have h10 :
      toPoly ((a.toBitVec &&& 0x22222222#64) *
        (b.toBitVec &&& 0x11111111#64) &&& 0x2222222222222222#64) =
      toPoly (a.toBitVec &&& 0x22222222#64) *
        toPoly (b.toBitVec &&& 0x11111111#64) :=
    stripePairPoly a.toBitVec b.toBitVec 1 0 (by decide) (by decide)
  have h11 :
      toPoly ((a.toBitVec &&& 0x22222222#64) *
        (b.toBitVec &&& 0x22222222#64) &&& 0x4444444444444444#64) =
      toPoly (a.toBitVec &&& 0x22222222#64) *
        toPoly (b.toBitVec &&& 0x22222222#64) :=
    stripePairPoly a.toBitVec b.toBitVec 1 1 (by decide) (by decide)
  have h12 :
      toPoly ((a.toBitVec &&& 0x22222222#64) *
        (b.toBitVec &&& 0x44444444#64) &&& 0x8888888888888888#64) =
      toPoly (a.toBitVec &&& 0x22222222#64) *
        toPoly (b.toBitVec &&& 0x44444444#64) :=
    stripePairPoly a.toBitVec b.toBitVec 1 2 (by decide) (by decide)
  have h13 :
      toPoly ((a.toBitVec &&& 0x22222222#64) *
        (b.toBitVec &&& 0x88888888#64) &&& 0x1111111111111111#64) =
      toPoly (a.toBitVec &&& 0x22222222#64) *
        toPoly (b.toBitVec &&& 0x88888888#64) :=
    stripePairPoly a.toBitVec b.toBitVec 1 3 (by decide) (by decide)
  have h20 :
      toPoly ((a.toBitVec &&& 0x44444444#64) *
        (b.toBitVec &&& 0x11111111#64) &&& 0x4444444444444444#64) =
      toPoly (a.toBitVec &&& 0x44444444#64) *
        toPoly (b.toBitVec &&& 0x11111111#64) :=
    stripePairPoly a.toBitVec b.toBitVec 2 0 (by decide) (by decide)
  have h21 :
      toPoly ((a.toBitVec &&& 0x44444444#64) *
        (b.toBitVec &&& 0x22222222#64) &&& 0x8888888888888888#64) =
      toPoly (a.toBitVec &&& 0x44444444#64) *
        toPoly (b.toBitVec &&& 0x22222222#64) :=
    stripePairPoly a.toBitVec b.toBitVec 2 1 (by decide) (by decide)
  have h22 :
      toPoly ((a.toBitVec &&& 0x44444444#64) *
        (b.toBitVec &&& 0x44444444#64) &&& 0x1111111111111111#64) =
      toPoly (a.toBitVec &&& 0x44444444#64) *
        toPoly (b.toBitVec &&& 0x44444444#64) :=
    stripePairPoly a.toBitVec b.toBitVec 2 2 (by decide) (by decide)
  have h23 :
      toPoly ((a.toBitVec &&& 0x44444444#64) *
        (b.toBitVec &&& 0x88888888#64) &&& 0x2222222222222222#64) =
      toPoly (a.toBitVec &&& 0x44444444#64) *
        toPoly (b.toBitVec &&& 0x88888888#64) :=
    stripePairPoly a.toBitVec b.toBitVec 2 3 (by decide) (by decide)
  have h30 :
      toPoly ((a.toBitVec &&& 0x88888888#64) *
        (b.toBitVec &&& 0x11111111#64) &&& 0x8888888888888888#64) =
      toPoly (a.toBitVec &&& 0x88888888#64) *
        toPoly (b.toBitVec &&& 0x11111111#64) :=
    stripePairPoly a.toBitVec b.toBitVec 3 0 (by decide) (by decide)
  have h31 :
      toPoly ((a.toBitVec &&& 0x88888888#64) *
        (b.toBitVec &&& 0x22222222#64) &&& 0x1111111111111111#64) =
      toPoly (a.toBitVec &&& 0x88888888#64) *
        toPoly (b.toBitVec &&& 0x22222222#64) :=
    stripePairPoly a.toBitVec b.toBitVec 3 1 (by decide) (by decide)
  have h32 :
      toPoly ((a.toBitVec &&& 0x88888888#64) *
        (b.toBitVec &&& 0x44444444#64) &&& 0x2222222222222222#64) =
      toPoly (a.toBitVec &&& 0x88888888#64) *
        toPoly (b.toBitVec &&& 0x44444444#64) :=
    stripePairPoly a.toBitVec b.toBitVec 3 2 (by decide) (by decide)
  have h33 :
      toPoly ((a.toBitVec &&& 0x88888888#64) *
        (b.toBitVec &&& 0x88888888#64) &&& 0x4444444444444444#64) =
      toPoly (a.toBitVec &&& 0x88888888#64) *
        toPoly (b.toBitVec &&& 0x88888888#64) :=
    stripePairPoly a.toBitVec b.toBitVec 3 3 (by decide) (by decide)
  rw [h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]
  ring

/-- Two word folds agree with the specification's double-width reduction. -/
theorem reduceWide_eq (lo hi : UInt64) : (reduceWide lo hi).toBitVec =
    reduce (lo.toBitVec.setWidth 128 ^^^ (hi.toBitVec.setWidth 128 <<< 64)) := by
  unfold reduceWide reduce foldStep
  rw [cmul_comm, cmul_tail, cmul_comm, cmul_tail]
  change (lo.toBitVec ^^^ hi.toBitVec ^^^ (hi.toBitVec <<< 1) ^^^
    (hi.toBitVec <<< 3) ^^^ (hi.toBitVec <<< 4) ^^^
    ((hi.toBitVec >>> 63) ^^^ (hi.toBitVec >>> 61) ^^^ (hi.toBitVec >>> 60)) ^^^
    (((hi.toBitVec >>> 63) ^^^ (hi.toBitVec >>> 61) ^^^ (hi.toBitVec >>> 60)) <<< 1) ^^^
    (((hi.toBitVec >>> 63) ^^^ (hi.toBitVec >>> 61) ^^^ (hi.toBitVec >>> 60)) <<< 3) ^^^
    (((hi.toBitVec >>> 63) ^^^ (hi.toBitVec >>> 61) ^^^ (hi.toBitVec >>> 60)) <<< 4)) = _
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  interval_cases i <;>
    simp [highHalf, lowHalf, zeroExtendTo, BitVec.getLsbD_of_ge, Bool.xor_comm, Bool.xor_left_comm]

/-- Splitting a word at bit 32 splits its denoted polynomial. -/
theorem splitPoly32 (a : BitVec 64) :
    toPoly a = toPoly ((a >>> 32).setWidth 32) * X^32 + toPoly (a.setWidth 32) := by
  rw [toPoly_split a 32 (by omega)]
  congr 1
  · congr 1
    rw [toPoly_eq_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi : i < 32 := Finset.mem_range.mp hi
    simp only [BitVec.toNat_setWidth, Nat.testBit_mod_two_pow, hi, decide_true,
      Bool.true_and, BitVec.toNat_ushiftRight, Nat.testBit_shiftRight, Nat.add_comm]
  · rw [toPoly_eq_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi : i < 32 := Finset.mem_range.mp hi
    simp only [BitVec.toNat_setWidth, Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]

private theorem combineMid (lo hi mid : BitVec 64) :
    (lo ^^^ (mid <<< 32)).setWidth 128 ^^^
      ((hi ^^^ (mid >>> 32)).setWidth 128 <<< 64) =
    lo.setWidth 128 ^^^ (mid.setWidth 128 <<< 32) ^^^ (hi.setWidth 128 <<< 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  interval_cases i <;> simp [BitVec.getLsbD_of_ge,
    Bool.xor_comm]

/-- Recombining Karatsuba halves preserves the full denoted polynomial. -/
theorem widePoly (lo hi mid : BitVec 64) :
    toPoly ((lo ^^^ (mid <<< 32)).setWidth 128 ^^^
      ((hi ^^^ (mid >>> 32)).setWidth 128 <<< 64)) =
      toPoly lo + toPoly mid * X^32 + toPoly hi * X^64 := by
  rw [combineMid, toPoly_xor, toPoly_xor,
    toPoly_shiftLeft_no_overflow _ (show (mid.setWidth 128).toNat < 2^64 from by
      simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
        (lt_trans mid.isLt (by decide : 2^64 < 2^128))] using mid.isLt) (by omega),
    toPoly_shiftLeft_no_overflow _ (show (hi.setWidth 128).toNat < 2^64 from by
      simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
        (lt_trans hi.isLt (by decide : 2^64 < 2^128))] using hi.isLt) (by omega)]
  simp only [show ∀ a : BitVec 64, toPoly (a.setWidth 128) = toPoly a from
    fun a => toPoly_zeroExtendTo a (by omega)]

end BF64.Word
