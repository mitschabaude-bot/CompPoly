/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Routing

/-! # Bit routing and bijectivity of register-block transposition -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace AdditiveNTT.Bitsliced

private theorem transpose0_get (a : Block) (i : Fin 64) :
    (transpose0 a).get i =
      if Nat.testBit i.val 0 then
        a.get i ^^^ (((a.get (flip 0 i) >>> UInt64.ofNat (2 ^ (0 : Fin 6).val)) ^^^
          a.get i) &&& mask 0)
      else
        a.get i ^^^ ((((a.get i >>> UInt64.ofNat (2 ^ (0 : Fin 6).val)) ^^^
          a.get (flip 0 i)) &&& mask 0) <<< UInt64.ofNat (2 ^ (0 : Fin 6).val)) := by
  fin_cases i <;> rfl

/-- Exchange pass 0 swaps exactly its row and column coordinate bits. -/
theorem bit_transpose0 (a : Block) (i j : Fin 64) :
    bit (transpose0 a) i j = bit a (route 0 (i, j)).1 (route 0 (i, j)).2 := by
  simp only [bit, transpose0_get]
  by_cases hi : Nat.testBit i.val 0 = true
  · rw [ite_eq_left hi]
    have hb := upper_bit 0 j (a.get (flip 0 i)) (a.get i)
    erw [hb]
    cases hj : Nat.testBit j.val 0 <;> simp [route, hi, hj]
  · have hf : Nat.testBit i.val 0 = false := Bool.eq_false_iff.mpr hi
    rw [ite_eq_right hi]
    have hb := lower_bit 0 j (a.get i) (a.get (flip 0 i))
    erw [hb]
    cases hj : Nat.testBit j.val 0 <;> simp [route, hf, hj]

private theorem transpose1_get (a : Block) (i : Fin 64) :
    (transpose1 a).get i =
      if Nat.testBit i.val 1 then
        a.get i ^^^ (((a.get (flip 1 i) >>> UInt64.ofNat (2 ^ (1 : Fin 6).val)) ^^^
          a.get i) &&& mask 1)
      else
        a.get i ^^^ ((((a.get i >>> UInt64.ofNat (2 ^ (1 : Fin 6).val)) ^^^
          a.get (flip 1 i)) &&& mask 1) <<< UInt64.ofNat (2 ^ (1 : Fin 6).val)) := by
  fin_cases i <;> rfl

/-- Exchange pass 1 swaps exactly its row and column coordinate bits. -/
theorem bit_transpose1 (a : Block) (i j : Fin 64) :
    bit (transpose1 a) i j = bit a (route 1 (i, j)).1 (route 1 (i, j)).2 := by
  simp only [bit, transpose1_get]
  by_cases hi : Nat.testBit i.val 1 = true
  · rw [ite_eq_left hi]
    have hb := upper_bit 1 j (a.get (flip 1 i)) (a.get i)
    erw [hb]
    cases hj : Nat.testBit j.val 1 <;> simp [route, hi, hj]
  · have hf : Nat.testBit i.val 1 = false := Bool.eq_false_iff.mpr hi
    rw [ite_eq_right hi]
    have hb := lower_bit 1 j (a.get i) (a.get (flip 1 i))
    erw [hb]
    cases hj : Nat.testBit j.val 1 <;> simp [route, hf, hj]

private theorem transpose2_get (a : Block) (i : Fin 64) :
    (transpose2 a).get i =
      if Nat.testBit i.val 2 then
        a.get i ^^^ (((a.get (flip 2 i) >>> UInt64.ofNat (2 ^ (2 : Fin 6).val)) ^^^
          a.get i) &&& mask 2)
      else
        a.get i ^^^ ((((a.get i >>> UInt64.ofNat (2 ^ (2 : Fin 6).val)) ^^^
          a.get (flip 2 i)) &&& mask 2) <<< UInt64.ofNat (2 ^ (2 : Fin 6).val)) := by
  fin_cases i <;> rfl

/-- Exchange pass 2 swaps exactly its row and column coordinate bits. -/
theorem bit_transpose2 (a : Block) (i j : Fin 64) :
    bit (transpose2 a) i j = bit a (route 2 (i, j)).1 (route 2 (i, j)).2 := by
  simp only [bit, transpose2_get]
  by_cases hi : Nat.testBit i.val 2 = true
  · rw [ite_eq_left hi]
    have hb := upper_bit 2 j (a.get (flip 2 i)) (a.get i)
    erw [hb]
    cases hj : Nat.testBit j.val 2 <;> simp [route, hi, hj]
  · have hf : Nat.testBit i.val 2 = false := Bool.eq_false_iff.mpr hi
    rw [ite_eq_right hi]
    have hb := lower_bit 2 j (a.get i) (a.get (flip 2 i))
    erw [hb]
    cases hj : Nat.testBit j.val 2 <;> simp [route, hf, hj]

private theorem transpose3_get (a : Block) (i : Fin 64) :
    (transpose3 a).get i =
      if Nat.testBit i.val 3 then
        a.get i ^^^ (((a.get (flip 3 i) >>> UInt64.ofNat (2 ^ (3 : Fin 6).val)) ^^^
          a.get i) &&& mask 3)
      else
        a.get i ^^^ ((((a.get i >>> UInt64.ofNat (2 ^ (3 : Fin 6).val)) ^^^
          a.get (flip 3 i)) &&& mask 3) <<< UInt64.ofNat (2 ^ (3 : Fin 6).val)) := by
  fin_cases i <;> rfl

/-- Exchange pass 3 swaps exactly its row and column coordinate bits. -/
theorem bit_transpose3 (a : Block) (i j : Fin 64) :
    bit (transpose3 a) i j = bit a (route 3 (i, j)).1 (route 3 (i, j)).2 := by
  simp only [bit, transpose3_get]
  by_cases hi : Nat.testBit i.val 3 = true
  · rw [ite_eq_left hi]
    have hb := upper_bit 3 j (a.get (flip 3 i)) (a.get i)
    erw [hb]
    cases hj : Nat.testBit j.val 3 <;> simp [route, hi, hj]
  · have hf : Nat.testBit i.val 3 = false := Bool.eq_false_iff.mpr hi
    rw [ite_eq_right hi]
    have hb := lower_bit 3 j (a.get i) (a.get (flip 3 i))
    erw [hb]
    cases hj : Nat.testBit j.val 3 <;> simp [route, hf, hj]

private theorem transpose4_get (a : Block) (i : Fin 64) :
    (transpose4 a).get i =
      if Nat.testBit i.val 4 then
        a.get i ^^^ (((a.get (flip 4 i) >>> UInt64.ofNat (2 ^ (4 : Fin 6).val)) ^^^
          a.get i) &&& mask 4)
      else
        a.get i ^^^ ((((a.get i >>> UInt64.ofNat (2 ^ (4 : Fin 6).val)) ^^^
          a.get (flip 4 i)) &&& mask 4) <<< UInt64.ofNat (2 ^ (4 : Fin 6).val)) := by
  fin_cases i <;> rfl

/-- Exchange pass 4 swaps exactly its row and column coordinate bits. -/
theorem bit_transpose4 (a : Block) (i j : Fin 64) :
    bit (transpose4 a) i j = bit a (route 4 (i, j)).1 (route 4 (i, j)).2 := by
  simp only [bit, transpose4_get]
  by_cases hi : Nat.testBit i.val 4 = true
  · rw [ite_eq_left hi]
    have hb := upper_bit 4 j (a.get (flip 4 i)) (a.get i)
    erw [hb]
    cases hj : Nat.testBit j.val 4 <;> simp [route, hi, hj]
  · have hf : Nat.testBit i.val 4 = false := Bool.eq_false_iff.mpr hi
    rw [ite_eq_right hi]
    have hb := lower_bit 4 j (a.get i) (a.get (flip 4 i))
    erw [hb]
    cases hj : Nat.testBit j.val 4 <;> simp [route, hf, hj]

private theorem transpose5_get (a : Block) (i : Fin 64) :
    (transpose5 a).get i =
      if Nat.testBit i.val 5 then
        a.get i ^^^ (((a.get (flip 5 i) >>> UInt64.ofNat (2 ^ (5 : Fin 6).val)) ^^^
          a.get i) &&& mask 5)
      else
        a.get i ^^^ ((((a.get i >>> UInt64.ofNat (2 ^ (5 : Fin 6).val)) ^^^
          a.get (flip 5 i)) &&& mask 5) <<< UInt64.ofNat (2 ^ (5 : Fin 6).val)) := by
  fin_cases i <;> rfl

/-- Exchange pass 5 swaps exactly its row and column coordinate bits. -/
theorem bit_transpose5 (a : Block) (i j : Fin 64) :
    bit (transpose5 a) i j = bit a (route 5 (i, j)).1 (route 5 (i, j)).2 := by
  simp only [bit, transpose5_get]
  by_cases hi : Nat.testBit i.val 5 = true
  · rw [ite_eq_left hi]
    have hb := upper_bit 5 j (a.get (flip 5 i)) (a.get i)
    erw [hb]
    cases hj : Nat.testBit j.val 5 <;> simp [route, hi, hj]
  · have hf : Nat.testBit i.val 5 = false := Bool.eq_false_iff.mpr hi
    rw [ite_eq_right hi]
    have hb := lower_bit 5 j (a.get i) (a.get (flip 5 i))
    erw [hb]
    cases hj : Nat.testBit j.val 5 <;> simp [route, hf, hj]

/-- Two register blocks agree when all their planes agree. -/
@[ext] theorem Block.ext {a b : Block} (h : ∀ i : Fin 64, a.get i = b.get i) : a = b := by
  cases a
  cases b
  congr 1
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h 5
  · exact h 6
  · exact h 7
  · exact h 8
  · exact h 9
  · exact h 10
  · exact h 11
  · exact h 12
  · exact h 13
  · exact h 14
  · exact h 15
  · exact h 16
  · exact h 17
  · exact h 18
  · exact h 19
  · exact h 20
  · exact h 21
  · exact h 22
  · exact h 23
  · exact h 24
  · exact h 25
  · exact h 26
  · exact h 27
  · exact h 28
  · exact h 29
  · exact h 30
  · exact h 31
  · exact h 32
  · exact h 33
  · exact h 34
  · exact h 35
  · exact h 36
  · exact h 37
  · exact h 38
  · exact h 39
  · exact h 40
  · exact h 41
  · exact h 42
  · exact h 43
  · exact h 44
  · exact h 45
  · exact h 46
  · exact h 47
  · exact h 48
  · exact h 49
  · exact h 50
  · exact h 51
  · exact h 52
  · exact h 53
  · exact h 54
  · exact h 55
  · exact h 56
  · exact h 57
  · exact h 58
  · exact h 59
  · exact h 60
  · exact h 61
  · exact h 62
  · exact h 63

/-- Two register blocks agree when all their bits agree. -/
theorem Block.bit_ext {a b : Block} (h : ∀ i j : Fin 64, bit a i j = bit b i j) : a = b := by
  apply Block.ext
  intro i
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact h i ⟨j, hj⟩

/-- Exchanging all six coordinate bits exchanges the two indices. -/
theorem route_all (i j : Fin 64) :
    route 0 (route 1 (route 2 (route 3 (route 4 (route 5 (i, j)))))) = (j, i) := by
  revert i j
  decide

/-- Every output bit is the input bit with its coordinates exchanged. -/
theorem bit_transpose (a : Block) (i j : Fin 64) : bit (transpose a) i j = bit a j i := by
  simp only [transpose, bit_transpose5, bit_transpose4, bit_transpose3,
    bit_transpose2, bit_transpose1, bit_transpose0]
  have h := route_all i j
  simpa only [Prod.eta] using congrArg (fun p => bit a p.1 p.2) h

/-- Transposing twice recovers every plane and lane. -/
theorem transpose_involutive : Function.Involutive transpose := by
  intro a
  apply Block.bit_ext
  intro i j
  simp only [bit_transpose]

/-- A second register transpose recovers the input block. -/
@[simp] theorem transpose_transpose (a : Block) : transpose (transpose a) = a :=
  transpose_involutive a

/-- Transposition is a bijection of the complete sixty-four-lane block. -/
theorem transpose_bijective : Function.Bijective transpose := transpose_involutive.bijective

/-- The certified change between lane words and bit planes. -/
def transposeEquiv : Block ≃ Block :=
  { toFun := transpose
    invFun := transpose
    left_inv := transpose_involutive
    right_inv := transpose_involutive }

end AdditiveNTT.Bitsliced
