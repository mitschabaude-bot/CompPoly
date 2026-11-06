/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Block
import Mathlib.Tactic.FinCases

/-! # Bit routing and bijectivity of register-block transposition -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace AdditiveNTT.Bitsliced

@[simp] theorem Block.get_ofFn (f : Fin 64 → UInt64) (i : Fin 64) :
    (Block.ofFn f).get i = f i := by
  fin_cases i <;> rfl

/-- Flip one of the six coordinate bits. -/
def flip (k : Fin 6) (i : Fin 64) : Fin 64 :=
  ⟨i.val ^^^ 2 ^ k.val, Nat.xor_lt_two_pow i.isLt
    (Nat.pow_lt_pow_right (by decide) k.isLt)⟩

/-- The low half of each bit-index exchange group. -/
def mask (k : Fin 6) : UInt64 :=
  if k.val = 0 then 6148914691236517205
  else if k.val = 1 then 3689348814741910323
  else if k.val = 2 then 1085102592571150095
  else if k.val = 3 then 71777214294589695
  else if k.val = 4 then 281470681808895
  else 4294967295

/-- A scalar coordinate of a register block. -/
def bit (a : Block) (i j : Fin 64) : Bool := (a.get i).toBitVec.getLsb j

/-- Swap the selected row and column index bits. -/
def route (k : Fin 6) (p : Fin 64 × Fin 64) : Fin 64 × Fin 64 :=
  if Nat.testBit p.1.val k.val = Nat.testBit p.2.val k.val then p
  else (flip k p.1, flip k p.2)

theorem lower_bit (k : Fin 6) (j : Fin 64) (x y : UInt64) :
    (x ^^^ ((((x >>> UInt64.ofNat (2 ^ k.val)) ^^^ y) &&& mask k) <<<
        UInt64.ofNat (2 ^ k.val))).toBitVec.getLsb j =
      if Nat.testBit j.val k.val then y.toBitVec.getLsb (flip k j)
      else x.toBitVec.getLsb j := by
  fin_cases k <;> fin_cases j <;>
    simp [mask, flip, Nat.testBit]

theorem upper_bit (k : Fin 6) (j : Fin 64) (x y : UInt64) :
    (y ^^^ (((x >>> UInt64.ofNat (2 ^ k.val)) ^^^ y) &&& mask k)).toBitVec.getLsb j =
      if Nat.testBit j.val k.val then y.toBitVec.getLsb j
      else x.toBitVec.getLsb (flip k j) := by
  fin_cases k <;> fin_cases j <;>
    simp [mask, flip, Nat.testBit]
  all_goals simp only [Bool.xor_left_comm, Bool.xor_self, Bool.xor_false]

end AdditiveNTT.Bitsliced
