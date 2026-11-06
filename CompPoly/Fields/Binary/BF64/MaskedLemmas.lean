/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Masked

/-! # Carry-free masked integer products -/

public section

namespace BF64.Word.MaskedLemmas
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem bit0_add (a b : Nat) :
    (a + b).testBit 0 = (a.testBit 0 ^^ b.testBit 0) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      simp [Nat.testBit_zero, Nat.add_mod, ha, hb]

private theorem quot8 (a b c d e f g h k : Nat) (hk : k < 16) :
    ((a &&& 0x1111111111111111) + (b &&& 0x1111111111111111) +
      (c &&& 0x1111111111111111) + (d &&& 0x1111111111111111) +
      (e &&& 0x1111111111111111) + (f &&& 0x1111111111111111) +
      (g &&& 0x1111111111111111) + (h &&& 0x1111111111111111)) / 2 ^ (4*k) =
    (a &&& 0x1111111111111111) / 2 ^ (4*k) + (b &&& 0x1111111111111111) / 2 ^ (4*k) +
      (c &&& 0x1111111111111111) / 2 ^ (4*k) + (d &&& 0x1111111111111111) / 2 ^ (4*k) +
      (e &&& 0x1111111111111111) / 2 ^ (4*k) + (f &&& 0x1111111111111111) / 2 ^ (4*k) +
      (g &&& 0x1111111111111111) / 2 ^ (4*k) + (h &&& 0x1111111111111111) / 2 ^ (4*k) := by
  have bound (x : Nat) : (x &&& 0x1111111111111111) % 2 ^ (4*k) ≤
      0x1111111111111111 % 2 ^ (4*k) := by
    rw [Nat.and_mod_two_pow]
    exact Nat.and_le_right
  have ha := bound a
  have hb := bound b
  have hc := bound c
  have hd := bound d
  have he := bound e
  have hf := bound f
  have hg := bound g
  have hh := bound h
  interval_cases k <;> norm_num at * <;> omega

/-- Eight sparse streams leave enough space for integer carries. -/
theorem mask_add8_nat (a b c d e f g h : Nat) :
    (((a &&& 0x1111111111111111) + (b &&& 0x1111111111111111) +
      (c &&& 0x1111111111111111) + (d &&& 0x1111111111111111) +
      (e &&& 0x1111111111111111) + (f &&& 0x1111111111111111) +
      (g &&& 0x1111111111111111) + (h &&& 0x1111111111111111)) &&& 0x1111111111111111) =
    ((a &&& 0x1111111111111111) ^^^ (b &&& 0x1111111111111111) ^^^
      (c &&& 0x1111111111111111) ^^^ (d &&& 0x1111111111111111) ^^^
      (e &&& 0x1111111111111111) ^^^ (f &&& 0x1111111111111111) ^^^
      (g &&& 0x1111111111111111) ^^^ (h &&& 0x1111111111111111)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_xor]
  by_cases hm : Nat.testBit 0x1111111111111111 i = true
  · have hi : i < 64 := by
      by_contra hn
      have hb : 0x1111111111111111 < 2 ^ i := lt_of_lt_of_le
        (by decide : 0x1111111111111111 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) (by omega))
      have hz := Nat.testBit_lt_two_pow hb
      rw [hz] at hm
      contradiction
    have hm' := hm
    interval_cases i <;> norm_num [Nat.testBit_eq_decide_div_mod_eq] at hm
    all_goals simp only [hm', Bool.and_true]
    all_goals conv_lhs => rw [show ∀ (x i : Nat), x.testBit i = (x / 2 ^ i).testBit 0 from
      fun x i => by simpa only [Nat.zero_add] using
        (Nat.testBit_div_two_pow (n := i) x 0).symm]
    all_goals first
      | rw [show 0 = 4 * 0 from rfl, quot8 _ _ _ _ _ _ _ _ 0 (by decide)]
      | rw [show 4 = 4 * 1 from rfl, quot8 _ _ _ _ _ _ _ _ 1 (by decide)]
      | rw [show 8 = 4 * 2 from rfl, quot8 _ _ _ _ _ _ _ _ 2 (by decide)]
      | rw [show 12 = 4 * 3 from rfl, quot8 _ _ _ _ _ _ _ _ 3 (by decide)]
      | rw [show 16 = 4 * 4 from rfl, quot8 _ _ _ _ _ _ _ _ 4 (by decide)]
      | rw [show 20 = 4 * 5 from rfl, quot8 _ _ _ _ _ _ _ _ 5 (by decide)]
      | rw [show 24 = 4 * 6 from rfl, quot8 _ _ _ _ _ _ _ _ 6 (by decide)]
      | rw [show 28 = 4 * 7 from rfl, quot8 _ _ _ _ _ _ _ _ 7 (by decide)]
      | rw [show 32 = 4 * 8 from rfl, quot8 _ _ _ _ _ _ _ _ 8 (by decide)]
      | rw [show 36 = 4 * 9 from rfl, quot8 _ _ _ _ _ _ _ _ 9 (by decide)]
      | rw [show 40 = 4 * 10 from rfl, quot8 _ _ _ _ _ _ _ _ 10 (by decide)]
      | rw [show 44 = 4 * 11 from rfl, quot8 _ _ _ _ _ _ _ _ 11 (by decide)]
      | rw [show 48 = 4 * 12 from rfl, quot8 _ _ _ _ _ _ _ _ 12 (by decide)]
      | rw [show 52 = 4 * 13 from rfl, quot8 _ _ _ _ _ _ _ _ 13 (by decide)]
      | rw [show 56 = 4 * 14 from rfl, quot8 _ _ _ _ _ _ _ _ 14 (by decide)]
      | rw [show 60 = 4 * 15 from rfl, quot8 _ _ _ _ _ _ _ _ 15 (by decide)]
    all_goals simp only [Nat.mul_zero, bit0_add, Nat.testBit_div_two_pow, Nat.zero_add,
      Nat.testBit_and, hm', Bool.and_true]
  · have hm' : Nat.testBit 0x1111111111111111 i = false := Bool.eq_false_iff.mpr hm
    simp only [hm', Bool.and_false, Bool.false_bne]

private theorem step16 (x m : Nat) (hm : m % 16 = 1) :
    x &&& m = x % 2 + 16 * ((x / 16) &&& (m / 16)) := by
  have hlo : (x &&& m) % 16 = x % 2 := by
    change (x &&& m) % 2^4 = x % 2
    rw [Nat.and_mod_two_pow]
    change (x % 16) &&& (m % 16) = x % 2
    rw [hm, Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)]
  have hhi : (x &&& m) / 16 = (x / 16) &&& (m / 16) := by
    simpa only [Nat.shiftRight_eq_div_pow] using
      (Nat.shiftRight_and_distrib (i := 4) (a := x) (b := m))
  have h := Nat.mod_add_div (x &&& m) 16
  omega

private theorem bitNat (x i : Nat) :
    (if x.testBit i then 1 else 0) = x / 2^i % 2 := by
  rcases Nat.mod_two_eq_zero_or_one (x / 2^i) with h | h <;>
    simp [Nat.testBit_eq_decide_div_mod_eq, h]

/-- The low 32-bit stripe is the sum of its eight base-16 digits. -/
theorem stripe32 (x : Nat) :
    x &&& 0x11111111 =
      1 * (if x.testBit 0 then 1 else 0) +
      16 * (if x.testBit 4 then 1 else 0) +
      256 * (if x.testBit 8 then 1 else 0) +
      4096 * (if x.testBit 12 then 1 else 0) +
      65536 * (if x.testBit 16 then 1 else 0) +
      1048576 * (if x.testBit 20 then 1 else 0) +
      16777216 * (if x.testBit 24 then 1 else 0) +
      268435456 * (if x.testBit 28 then 1 else 0) := by
  simp only [bitNat]
  have h0 := step16 (x / 1) 286331153 (by decide)
  have h1 := step16 (x / 16) 17895697 (by decide)
  have h2 := step16 (x / 256) 1118481 (by decide)
  have h3 := step16 (x / 4096) 69905 (by decide)
  have h4 := step16 (x / 65536) 4369 (by decide)
  have h5 := step16 (x / 1048576) 273 (by decide)
  have h6 := step16 (x / 16777216) 17 (by decide)
  have h7 := step16 (x / 268435456) 1 (by decide)
  norm_num only [Nat.div_one, Nat.reduceDiv, Nat.div_div_eq_div_mul, Nat.reduceMul,
    Nat.and_zero, Nat.mul_zero, Nat.add_zero] at *
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  ring


private theorem shiftedStripe (x i : Nat) (hi : i < 8) :
    (((x &&& 0x11111111) <<< (4*i)) &&& 0x1111111111111111) =
      (x &&& 0x11111111) <<< (4*i) := by
  rw [Nat.shiftLeft_and_distrib, Nat.and_assoc]
  have h : ((0x11111111 : Nat) <<< (4*i)) &&& 0x1111111111111111 =
      0x11111111 <<< (4*i) := by
    interval_cases i <;> decide
  rw [h]

/-- Masking an integer stripe product recovers the coefficient parities. -/
theorem stripeProduct (a b : Nat) :
    (((a &&& 0x11111111) * (b &&& 0x11111111)) &&& 0x1111111111111111) =
      (if a.testBit 0 then (b &&& 0x11111111) <<< 0 else 0) ^^^
      (if a.testBit 4 then (b &&& 0x11111111) <<< 4 else 0) ^^^
      (if a.testBit 8 then (b &&& 0x11111111) <<< 8 else 0) ^^^
      (if a.testBit 12 then (b &&& 0x11111111) <<< 12 else 0) ^^^
      (if a.testBit 16 then (b &&& 0x11111111) <<< 16 else 0) ^^^
      (if a.testBit 20 then (b &&& 0x11111111) <<< 20 else 0) ^^^
      (if a.testBit 24 then (b &&& 0x11111111) <<< 24 else 0) ^^^
      (if a.testBit 28 then (b &&& 0x11111111) <<< 28 else 0) := by
  have hm (i : Nat) (hi : i < 8) :
      ((if a.testBit (4*i) then (b &&& 0x11111111) <<< (4*i) else 0) &&&
        0x1111111111111111) =
      (if a.testBit (4*i) then (b &&& 0x11111111) <<< (4*i) else 0) := by
    split
    · exact shiftedStripe b i hi
    · rfl
  have hs := mask_add8_nat
    (if a.testBit 0 then (b &&& 0x11111111) <<< 0 else 0)
    (if a.testBit 4 then (b &&& 0x11111111) <<< 4 else 0)
    (if a.testBit 8 then (b &&& 0x11111111) <<< 8 else 0)
    (if a.testBit 12 then (b &&& 0x11111111) <<< 12 else 0)
    (if a.testBit 16 then (b &&& 0x11111111) <<< 16 else 0)
    (if a.testBit 20 then (b &&& 0x11111111) <<< 20 else 0)
    (if a.testBit 24 then (b &&& 0x11111111) <<< 24 else 0)
    (if a.testBit 28 then (b &&& 0x11111111) <<< 28 else 0)
  simp only [hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide),
    hm 4 (by decide), hm 5 (by decide), hm 6 (by decide), hm 7 (by decide)] at hs
  rw [stripe32 a]
  simp only [Nat.add_mul, mul_ite, Nat.mul_one, Nat.mul_zero,
    ite_mul, Nat.zero_mul]
  simp only [Nat.shiftLeft_eq] at hs
  simp only [Nat.shiftLeft_eq, Nat.reduceMul, Nat.reducePow, Nat.mul_zero,
    Nat.mul_one, Nat.one_mul] at hs ⊢
  simpa only [Nat.mul_comm] using hs


private theorem bvOfShift (x n : Nat) :
    BitVec.ofNat 64 (x <<< n) = (BitVec.ofNat 64 x) <<< n := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq, Nat.mul_mod]

private theorem bvOfIte (c : Bool) (x y : Nat) :
    BitVec.ofNat 64 (if c then x else y) =
      if c then BitVec.ofNat 64 x else BitVec.ofNat 64 y := by cases c <;> rfl

/-- An integer stripe product equals the complete carry-less polynomial product. -/
theorem stripeBV (a b : BitVec 64) :
    (((a &&& (0x11111111#64)) * (b &&& (0x11111111#64))) &&& (0x1111111111111111#64)) =
      BinaryField.carryLessMul (w := 64) ((a &&& (0x11111111#64)).setWidth 32)
        ((b &&& (0x11111111#64)).setWidth 32) := by
  have hs := congrArg (BitVec.ofNat 64) (stripeProduct a.toNat b.toNat)
  simp only [BitVec.ofNat_and, BitVec.ofNat_mul, BitVec.ofNat_xor,
    BitVec.ofNat_toNat, BitVec.setWidth_eq, bvOfShift, bvOfIte] at hs
  refine hs.trans ?_
  rw [BinaryField.carryLessMul_unfold]
  unfold BinaryField.zeroExtendTo
  simp only [Fin.foldl_succ_last, Fin.foldl_zero, Fin.val_castSucc, Fin.val_last]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  norm_num [Nat.testBit_eq_decide_div_mod_eq, BitVec.zero_xor]
  have hb : BitVec.setWidth 64 (BitVec.setWidth 32 b) &&& (0x11111111#64) =
      b &&& (0x11111111#64) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp
  simp [BitVec.ofNat_eq_ofNat, hb, BitVec.getElem_eq_testBit_toNat,
    Nat.testBit_eq_decide_div_mod_eq]


end BF64.Word.MaskedLemmas
