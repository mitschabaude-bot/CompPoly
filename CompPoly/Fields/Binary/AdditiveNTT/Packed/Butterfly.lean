/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.FixedMapProofs
public import CompPoly.Fields.Binary.BF64.MaskedProofs

/-!
# Packed disjoint butterfly sweeps

A stage partitions a word buffer into disjoint ordered pairs. The sweep updates
each pair in place; its refinement reads both operands from the input stage.
-/

@[expose] public section

namespace AdditiveNTT.Packed

open BF64

/-- Fill contiguous storage without allocating a list of indices. -/
def tabulate (n : Nat) (f : Fin n → Word) : BF64.Packed.Buffer n :=
  Fin.foldl n (fun a i => BF64.Packed.write a i (f i)) ⟨BF64.Packed.zeros n, rfl⟩

@[simp] theorem read_tabulate (n : Nat) (f : Fin n → Word) (i : Fin n) :
    BF64.Packed.read (tabulate n f) i = f i := by
  rw [tabulate, Fin.foldl_eq_finRange_foldl]
  exact BF64.Packed.read_ofFn n f i

/-- Store the two results of one butterfly. -/
@[inline] def updatePair {n k : Nat} (index : Fin k × Fin 2 → Fin n)
    (op : Fin k → Word → Word → Word × Word) (a : BF64.Packed.Buffer n)
    (j : Fin k) : BF64.Packed.Buffer n :=
  let u := BF64.Packed.read a (index (j, 0))
  let v := BF64.Packed.read a (index (j, 1))
  let out := op j u v
  BF64.Packed.write (BF64.Packed.write a (index (j, 0)) out.1) (index (j, 1)) out.2

private theorem read_updatePair {n k : Nat} (index : Fin k × Fin 2 → Fin n)
    (hinj : Function.Injective index) (op : Fin k → Word → Word → Word × Word)
    (a : BF64.Packed.Buffer n) (j t : Fin k) (b : Fin 2) :
    BF64.Packed.read (updatePair index op a j) (index (t, b)) =
      if j = t then
        if b = 0 then (op t (BF64.Packed.read a (index (t, 0)))
          (BF64.Packed.read a (index (t, 1)))).1
        else (op t (BF64.Packed.read a (index (t, 0)))
          (BF64.Packed.read a (index (t, 1)))).2
      else BF64.Packed.read a (index (t, b)) := by
  simp only [updatePair, BF64.Packed.read_write, hinj.eq_iff, Prod.mk.injEq]
  by_cases h : j = t
  · subst j
    fin_cases b <;> simp
  · simp only [h, false_and, ite_false]

/-- Apply a word butterfly to every disjoint pair, in increasing pair order. -/
@[specialize] def sweep {n k : Nat} (index : Fin k × Fin 2 → Fin n)
    (op : Fin k → Word → Word → Word × Word)
    (a : BF64.Packed.Buffer n) : BF64.Packed.Buffer n :=
  Fin.foldl k (updatePair index op) a

/-- Each sweep coordinate is the butterfly on its unchanged input pair. -/
theorem read_sweep {n k : Nat} (index : Fin k × Fin 2 → Fin n)
    (hinj : Function.Injective index) (op : Fin k → Word → Word → Word × Word)
    (a : BF64.Packed.Buffer n) (t : Fin k) (b : Fin 2) :
    BF64.Packed.read (sweep index op a) (index (t, b)) =
      if b = 0 then (op t (BF64.Packed.read a (index (t, 0)))
        (BF64.Packed.read a (index (t, 1)))).1
      else (op t (BF64.Packed.read a (index (t, 0)))
        (BF64.Packed.read a (index (t, 1)))).2 := by
  have aux (xs : List (Fin k)) (hx : xs.Nodup) (a : BF64.Packed.Buffer n) :
      BF64.Packed.read (xs.foldl (updatePair index op) a) (index (t, b)) =
        if t ∈ xs then
          if b = 0 then (op t (BF64.Packed.read a (index (t, 0)))
            (BF64.Packed.read a (index (t, 1)))).1
          else (op t (BF64.Packed.read a (index (t, 0)))
            (BF64.Packed.read a (index (t, 1)))).2
        else BF64.Packed.read a (index (t, b)) := by
    induction xs generalizing a with
    | nil => simp only [List.foldl_nil, List.not_mem_nil, ite_false]
    | cons j xs ih =>
      rw [List.nodup_cons] at hx
      rw [List.foldl_cons, ih hx.2]
      by_cases hj : j = t
      · subst j
        simp only [hx.1, ite_false, List.mem_cons, true_or, ite_true]
        simpa only [ite_true] using read_updatePair index hinj op a t t b
      · simp only [read_updatePair index hinj, hj, ite_false]
        simp only [List.mem_cons, Ne.symm hj, false_or]
  rw [sweep, Fin.foldl_eq_finRange_foldl,
    aux _ (List.nodup_finRange k) a, ite_eq_left (List.mem_finRange t)]

/-- A prepared or arithmetic product with one certified shared scalar. -/
structure Multiplier where
  /-- Scalar in the specification field. -/
  scalar : Word
  /-- Executable multiplication by this scalar. -/
  apply : Word → Word
  /-- Multiplication agrees with the field product. -/
  correct : ∀ a, (apply a).toField = scalar.toField * a.toField

/-- Masked multiplication for twiddles with little reuse. -/
def Multiplier.masked (t : Word) : Multiplier :=
  ⟨t, fun a => Word.mulMasked t a, fun a => Word.toField_mulMasked t a⟩

/-- Prepare a byte map once for all butterflies sharing a twiddle. -/
def Multiplier.prepared (t : Word) : Multiplier :=
  let m := Word.ByteMap.ofScalar t
  ⟨t, m.mul, fun a => Word.ByteMap.toField_mul t a⟩

/-- Normalized additive butterfly, with one shared-scalar product. -/
@[inline] def forwardPair (m : Multiplier) (u v : Word) : Word × Word :=
  let lo := Word.add u (m.apply v)
  (lo, Word.add lo v)

/-- The inverse normalized butterfly uses the same scalar and no division. -/
@[inline] def inversePair (m : Multiplier) (u v : Word) : Word × Word :=
  let hi := Word.add u v
  (Word.add u (m.apply hi), hi)

end AdditiveNTT.Packed
