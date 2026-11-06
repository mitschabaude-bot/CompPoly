/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.Bytes

/-!
# Machine-word arithmetic in the BF64 polynomial basis

`Word` erases to `UInt64`. Raw words are polynomial coordinates, independently of
characteristic-two field numerals. The specification map is `Word.toField`.
-/

@[expose] public section

namespace BF64

/-- Unboxed polynomial-basis carrier for the base field. -/
structure Word where
  /-- Coefficients of degrees zero through 63, least significant bit first. -/
  val : UInt64
  deriving DecidableEq, BEq, Inhabited, Repr

namespace Word

/-- Interpret polynomial coordinates in the existing field. -/
@[inline] def toField (a : Word) : BF64 := ofBitVec a.val.toBitVec

/-- Read the polynomial coordinates of the specification carrier. -/
@[inline] def ofField (a : BF64) : Word := ⟨UInt64.ofBitVec a.toBitVec⟩

@[simp] theorem toField_ofField (a : BF64) : toField (ofField a) = a := rfl
@[simp] theorem ofField_toField (a : Word) : ofField (toField a) = a := rfl

theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

/-- Raw coefficientwise XOR. -/
@[inline] def add (a b : Word) : Word := ⟨a.val ^^^ b.val⟩

@[simp] theorem toField_add (a b : Word) : toField (add a b) = toField a + toField b := rfl

/-- Multiply a polynomial word by `X`, folding the outgoing bit with `0x1b`. -/
@[inline] def xtime (a : UInt64) : UInt64 :=
  (a <<< 1) ^^^ (((0 : UInt64) - (a >>> 63)) &&& 0x1b)

/-- Scalar shift/XOR product. All loop state is passed as unboxed words. -/
def mulLoop : Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, acc => acc
  | n + 1, a, b, acc =>
    mulLoop n (xtime a) (b >>> 1) (acc ^^^ (((0 : UInt64) - (b &&& 1)) &&& a))

/-- Machine-counter version of the scalar product loop. -/
def mulLoopFast (n : UInt64) (a b acc : UInt64) : UInt64 :=
  if h : n = 0 then acc else
    mulLoopFast (n - 1) (xtime a) (b >>> 1) (acc ^^^ (((0 : UInt64) - (b &&& 1)) &&& a))
termination_by n.toNat
decreasing_by
  have hn : 0 < n.toNat := by
    have : n.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp hz)
    omega
  rw [UInt64.toNat_sub_of_le]
  · change n.toNat - 1 < n.toNat
    omega
  · change (1 : UInt64).toNat ≤ n.toNat
    exact hn

/-- Polynomial multiplication modulo `X^64 + X^4 + X^3 + X + 1`. -/
@[inline] def mul (a b : Word) : Word := ⟨mulLoopFast 64 a.val b.val 0⟩

/-- Squaring in the polynomial basis. -/
@[inline] def square (a : Word) : Word := mul a a

/-- The `2^n` Frobenius, as a scalar tail-recursive squaring chain. -/
def frobenius (a : Word) : Nat → Word
  | 0 => a
  | n + 1 => frobenius (square a) n

/-- Inversion by the degree-64 Itoh–Tsujii chain, including the zero input. -/
def inv (a : Word) : Word :=
  let u2 := mul (frobenius a 1) a
  let u3 := mul (frobenius u2 1) a
  let u6 := mul (frobenius u3 3) u3
  let u7 := mul (frobenius u6 1) a
  let u14 := mul (frobenius u7 7) u7
  let u15 := mul (frobenius u14 1) a
  let u30 := mul (frobenius u15 15) u15
  let u31 := mul (frobenius u30 1) a
  let u62 := mul (frobenius u31 31) u31
  let u63 := mul (frobenius u62 1) a
  square u63

instance : CompPoly.CanonicalNat Word :=
  CompPoly.CanonicalNat.ofBitVec (fun a => a.val.toBitVec)
    (fun a => ⟨UInt64.ofBitVec a⟩) (fun _ => rfl) (fun _ => rfl)

instance : CompPoly.ByteCodec Word := CompPoly.ByteCodec.ofCanonicalNat _

/-- Canonical coordinates agree with the specification, so the derived codecs agree. -/
@[simp] theorem canonicalNat_toField (a : Word) :
    CompPoly.CanonicalNat.toNat (toField a) = CompPoly.CanonicalNat.toNat a := rfl

end Word
end BF64
