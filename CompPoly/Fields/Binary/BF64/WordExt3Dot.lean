/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Binary.BF64.WordExt3Proofs
public import CompPoly.Fields.Binary.BF64.Packed

/-!
# Packed cubic-extension dot products

A buffer stores the three base-field coordinates consecutively. Dot products
accumulate five polynomial coefficients and reduce by `Y³ + Y + 1` once.
Base-field products accumulate as double-width carry-less words; only the three
output coordinates are reduced modulo the base-field polynomial.
-/

public section

namespace BF64.WordExt3

/-- Contiguous constant, linear and quadratic coordinates of `n` extension elements. -/
abbrev Buffer (n : Nat) := Packed.Buffer (3 * n)

/-- Load three consecutive base-field words. -/
@[inline] def read (a : Buffer n) (i : Fin n) : WordExt3 :=
  ⟨Packed.read a ⟨3 * i.val, by omega⟩,
    Packed.read a ⟨3 * i.val + 1, by omega⟩,
    Packed.read a ⟨3 * i.val + 2, by omega⟩⟩

/-- Materialize extension elements in coefficient order. -/
def ofFn (n : Nat) (f : Fin n → WordExt3) : Buffer n :=
  Packed.ofFn (3 * n) fun i =>
    let a := f ⟨i.val / 3, by omega⟩
    if i.val % 3 = 0 then a.c0 else if i.val % 3 = 1 then a.c1 else a.c2

/-- Packed coordinates recover the supplied extension elements. -/
@[simp] theorem read_ofFn (n : Nat) (f : Fin n → WordExt3) (i : Fin n) :
    read (ofFn n f) i = f i := by
  simp only [read, ofFn, Packed.read_ofFn]
  have h0 : 3 * i.val / 3 = i.val := by omega
  have h1 : (3 * i.val + 1) / 3 = i.val := by omega
  have h2 : (3 * i.val + 2) / 3 = i.val := by omega
  have r0 : 3 * i.val % 3 = 0 := by omega
  have r1 : (3 * i.val + 1) % 3 = 1 := by omega
  have r2 : (3 * i.val + 2) % 3 = 2 := by omega
  simp only [h0, h1, h2, r0, r1, r2, ↓reduceIte, Nat.reduceEqDiff]

private structure WideWord where
  lo : UInt64
  hi : UInt64

private theorem wideEta (a : WideWord) : (⟨a.lo, a.hi⟩ : WideWord) = a := by
  cases a
  rfl

@[inline] private def wideAdd (a b : WideWord) : WideWord :=
  ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩

@[inline] private def wideReduce (a : WideWord) : Word := ⟨Word.reduceWide a.lo a.hi⟩

@[inline] private def wideMul (a b : Word) : WideWord :=
  ⟨Word.clMulLo a.val b.val, Word.clMulHi a.val b.val⟩

private theorem wideReduce_add (a b : WideWord) :
    Word.toField (wideReduce (wideAdd a b)) =
      Word.toField (wideReduce a) + Word.toField (wideReduce b) := by
  apply BF64.ext
  change (Word.reduceWide (a.lo ^^^ b.lo) (a.hi ^^^ b.hi)).toBitVec =
    (Word.reduceWide a.lo a.hi).toBitVec ^^^ (Word.reduceWide b.lo b.hi).toBitVec
  simp only [Word.reduceWide, UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq', BitVec.ofNat_eq_ofNat, BitVec.toNat_umod,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  simp only [BitVec.shiftLeft_xor_distrib, BitVec.ushiftRight_xor_distrib]
  ac_rfl

private theorem wideReduce_mul (a b : Word) :
    Word.toField (wideReduce (wideMul a b)) = a.toField * b.toField := by
  exact Word.toField_mulMasked a b

private structure DotAcc where
  c0lo : UInt64
  c0hi : UInt64
  c1lo : UInt64
  c1hi : UInt64
  c2lo : UInt64
  c2hi : UInt64
  c3lo : UInt64
  c3hi : UInt64
  c4lo : UInt64
  c4hi : UInt64

private def dotAccZero : DotAcc := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[inline] private def dotAccReduce (a : DotAcc) : WordExt3 :=
  ⟨wideReduce (wideAdd ⟨a.c0lo, a.c0hi⟩ ⟨a.c3lo, a.c3hi⟩),
    wideReduce (wideAdd (wideAdd ⟨a.c1lo, a.c1hi⟩ ⟨a.c3lo, a.c3hi⟩) ⟨a.c4lo, a.c4hi⟩),
    wideReduce (wideAdd ⟨a.c2lo, a.c2hi⟩ ⟨a.c4lo, a.c4hi⟩)⟩

@[inline] private def dotAccStep (acc : DotAcc) (a b : WordExt3) : DotAcc :=
  let p0 := wideMul a.c0 b.c0
  let p1 := wideMul a.c1 b.c1
  let p2 := wideMul a.c2 b.c2
  let p01 := wideAdd (wideAdd (wideMul (Word.add a.c0 a.c1)
    (Word.add b.c0 b.c1)) p0) p1
  let p02 := wideAdd (wideAdd (wideMul (Word.add a.c0 a.c2)
    (Word.add b.c0 b.c2)) p0) p2
  let p12 := wideAdd (wideAdd (wideMul (Word.add a.c1 a.c2)
    (Word.add b.c1 b.c2)) p1) p2
  let r0 := wideAdd ⟨acc.c0lo, acc.c0hi⟩ p0
  let r1 := wideAdd ⟨acc.c1lo, acc.c1hi⟩ p01
  let r2 := wideAdd ⟨acc.c2lo, acc.c2hi⟩ (wideAdd p02 p1)
  let r3 := wideAdd ⟨acc.c3lo, acc.c3hi⟩ p12
  let r4 := wideAdd ⟨acc.c4lo, acc.c4hi⟩ p2
  ⟨r0.lo, r0.hi, r1.lo, r1.hi, r2.lo, r2.hi, r3.lo, r3.hi, r4.lo, r4.hi⟩

private theorem dotAccStep_agrees (acc : DotAcc) (a b : WordExt3) :
    toField (dotAccReduce (dotAccStep acc a b)) =
      toField (dotAccReduce acc) + toField a * toField b := by
  rw [← toField_mul, ← toField_add]
  apply congrArg toField
  dsimp only [dotAccReduce, dotAccStep, add, mul]
  congr 1 <;> apply Word.toField_injective <;>
    simp only [wideEta, wideReduce_add, wideReduce_mul, Word.toField_add,
      Word.toField_mulMasked] <;> ac_rfl

private theorem dotAccZero_agrees : toField (dotAccReduce dotAccZero) = 0 := by
  apply CompPoly.Extension.Ext.ext
  intro i
  fin_cases i <;> rfl

/-- Sum packed extension products, with a single cubic reduction after accumulation. -/
def dot (a b : Buffer n) : WordExt3 :=
  ((List.finRange n).foldl (fun acc i => dotAccStep acc (read a i) (read b i))
    dotAccZero) |> dotAccReduce

/-- Packed dot products agree with the specification sum on every buffer length. -/
@[simp] theorem toField_dot (a b : Buffer n) :
    toField (dot a b) =
      ((List.finRange n).map fun i => toField (read a i) * toField (read b i)).sum := by
  have hf : ∀ (xs : List (Fin n)) (acc : DotAcc),
      toField (dotAccReduce (xs.foldl
        (fun acc i => dotAccStep acc (read a i) (read b i)) acc)) =
      toField (dotAccReduce acc) +
        (xs.map fun i => toField (read a i) * toField (read b i)).sum := by
    intro xs
    induction xs with
    | nil => intro acc; simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    | cons i xs ih =>
      intro acc
      rw [List.foldl_cons, ih, dotAccStep_agrees]
      simp only [List.map_cons, List.sum_cons, add_assoc]
  exact (hf _ _).trans (by rw [dotAccZero_agrees, zero_add])

end BF64.WordExt3
