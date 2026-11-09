/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Scalar
public import CompPoly.Fields.Binary.BF64.Packed.Ext

/-! # Fused radix-four additive butterflies -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace AdditiveNTT.Packed
open BF64

/-- Four ordered field words kept together through a fused butterfly. -/
abbrev Quad := Word × Word × Word × Word

/-- Select one of four ordered field words. -/
@[inline] def Quad.get (q : Quad) (i : Fin 4) : Word :=
  if i.val = 0 then q.1 else if i.val = 1 then q.2.1
  else if i.val = 2 then q.2.2.1 else q.2.2.2

/-- The radix-four schedule shares one upper-stage and two lower-stage twiddles. -/
@[inline] def radix4 (t a b : Multiplier) (x0 x1 x2 x3 : Word) : Quad :=
  let u := forwardPair t x0 x2
  let v := forwardPair t x1 x3
  let lo := forwardPair a u.1 v.1
  let hi := forwardPair b u.2 v.2
  (lo.1, lo.2, hi.1, hi.2)

/-- Store four output words after reading the entire input group. -/
@[inline] def updateQuad {n k : Nat} (index : Fin k × Fin 4 → Fin n)
    (op : Fin k → Word → Word → Word → Word → Quad)
    (a : BF64.Packed.Buffer n) (j : Fin k) : BF64.Packed.Buffer n :=
  let out := op j (BF64.Packed.read a (index (j, 0)))
    (BF64.Packed.read a (index (j, 1))) (BF64.Packed.read a (index (j, 2)))
    (BF64.Packed.read a (index (j, 3)))
  BF64.Packed.write (BF64.Packed.write (BF64.Packed.write
    (BF64.Packed.write a (index (j, 0)) out.1)
      (index (j, 1)) out.2.1) (index (j, 2)) out.2.2.1) (index (j, 3)) out.2.2.2

/-- A disjoint four-word update preserves every other group. -/
theorem read_updateQuad {n k : Nat} (index : Fin k × Fin 4 → Fin n)
    (hinj : Function.Injective index) (op : Fin k → Word → Word → Word → Word → Quad)
    (a : BF64.Packed.Buffer n) (j t : Fin k) (b : Fin 4) :
    BF64.Packed.read (updateQuad index op a j) (index (t, b)) =
      if j = t then
        (op t (BF64.Packed.read a (index (t, 0))) (BF64.Packed.read a (index (t, 1)))
          (BF64.Packed.read a (index (t, 2))) (BF64.Packed.read a (index (t, 3)))).get b
      else BF64.Packed.read a (index (t, b)) := by
  simp only [updateQuad, BF64.Packed.read_write, hinj.eq_iff, Prod.mk.injEq]
  by_cases h : j = t
  · subst j
    fin_cases b <;> simp [Quad.get]
  · simp only [h, false_and, ite_false]

/-- Apply a fused butterfly to every disjoint four-word group. -/
@[specialize] def sweepQuad {n k : Nat} (index : Fin k × Fin 4 → Fin n)
    (op : Fin k → Word → Word → Word → Word → Quad)
    (a : BF64.Packed.Buffer n) : BF64.Packed.Buffer n := Fin.foldl k (updateQuad index op) a

/-- Each fused output depends only on its unchanged four-word input group. -/
theorem read_sweepQuad {n k : Nat} (index : Fin k × Fin 4 → Fin n)
    (hinj : Function.Injective index) (op : Fin k → Word → Word → Word → Word → Quad)
    (a : BF64.Packed.Buffer n) (t : Fin k) (b : Fin 4) :
    BF64.Packed.read (sweepQuad index op a) (index (t, b)) =
      (op t (BF64.Packed.read a (index (t, 0))) (BF64.Packed.read a (index (t, 1)))
        (BF64.Packed.read a (index (t, 2))) (BF64.Packed.read a (index (t, 3)))).get b := by
  have aux (xs : List (Fin k)) (hx : xs.Nodup) (a : BF64.Packed.Buffer n) :
      BF64.Packed.read (xs.foldl (updateQuad index op) a) (index (t, b)) =
        if t ∈ xs then
          (op t (BF64.Packed.read a (index (t, 0))) (BF64.Packed.read a (index (t, 1)))
            (BF64.Packed.read a (index (t, 2))) (BF64.Packed.read a (index (t, 3)))).get b
        else BF64.Packed.read a (index (t, b)) := by
    induction xs generalizing a with
    | nil => simp only [List.foldl_nil, List.not_mem_nil, ite_false]
    | cons j xs ih =>
      rw [List.nodup_cons] at hx
      rw [List.foldl_cons, ih hx.2]
      by_cases hj : j = t
      · subst j
        simp only [hx.1, ite_false, List.mem_cons, true_or, ite_true]
        simpa only [ite_true] using read_updateQuad index hinj op a t t b
      · simp only [read_updateQuad index hinj, hj, ite_false]
        simp only [List.mem_cons, Ne.symm hj, false_or]
  rw [sweepQuad, Fin.foldl_eq_finRange_foldl,
    aux _ (List.nodup_finRange k) a, ite_eq_left (List.mem_finRange t)]

/-- Arrange each four-word group as four contiguous equal-size slabs. -/
def quadIndex (blocks span : Nat) :
    Fin (blocks * span) × Fin 4 ≃ Fin (blocks * (4 * span)) where
  toFun p :=
    let q := finProdFinEquiv.symm p.1
    finProdFinEquiv (q.1, finProdFinEquiv (p.2, q.2))
  invFun j :=
    let q := finProdFinEquiv.symm j
    let r := finProdFinEquiv.symm q.2
    (finProdFinEquiv (q.1, r.2), r.1)
  left_inv p := by simp only [Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv j := by simp only [Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]

/-- A stage index separates the block, side and column coordinates. -/
theorem stageIndex_block_val (d : Nat) (i : Fin d) (lanes : Nat)
    (g : Fin (2 ^ (d - i.val - 1))) (v : Fin (2 ^ i.val * lanes)) (b : Fin 2) :
    (stageIndex d i lanes (finProdFinEquiv (g, v), b)).val =
      v.val + (2 ^ i.val * lanes) * (b.val + 2 * g.val) := by
  simp only [stageIndex_apply, Equiv.trans_apply, pairIndex, Equiv.coe_fn_mk,
    Equiv.symm_apply_apply]
  simp only [finCongr_apply, Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk]
  ring

/-- Four slabs contain the words of two consecutive transform stages. -/
theorem quad_word_count (d i lanes : Nat) (hi : i + 1 < d) :
    2 ^ (d - (i + 1) - 1) * (4 * (2 ^ i * lanes)) = 2 ^ d * lanes := by
  calc
    _ = 2 ^ (d - (i + 1) - 1) * (2 * (2 ^ (i + 1) * lanes)) := by
      rw [pow_succ]
      ring
    _ = _ := stage_word_count d ⟨i + 1, hi⟩ lanes

/-- The four-slab partition of two consecutive additive stages. -/
def quadStageIndex (d i lanes : Nat) (hi : i + 1 < d) :
    Fin (2 ^ (d - (i + 1) - 1) * (2 ^ i * lanes)) × Fin 4 ≃
      Fin (2 ^ d * lanes) :=
  (quadIndex _ _).trans (finCongr (quad_word_count d i lanes hi))

/-- A fused coordinate is its column plus its slab and block strides. -/
theorem quadStageIndex_val (d i lanes : Nat) (hi : i + 1 < d)
    (g : Fin (2 ^ (d - (i + 1) - 1))) (v : Fin (2 ^ i * lanes)) (b : Fin 4) :
    (quadStageIndex d i lanes hi (finProdFinEquiv (g, v), b)).val =
      v.val + (2 ^ i * lanes) * (b.val + 4 * g.val) := by
  simp only [quadStageIndex, quadIndex, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.symm_apply_apply]
  simp only [finCongr_apply, Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk]
  ring

/-- Each fused block contains exactly two lower-stage blocks. -/
theorem quad_lower_blocks (d i : Nat) (hi : i + 1 < d) :
    2 ^ (d - i - 1) = 2 * 2 ^ (d - (i + 1) - 1) := by
  have he : d - i - 1 = (d - (i + 1) - 1) + 1 := by omega
  rw [he, pow_succ, Nat.mul_comm]

/-- Select one of the two lower-stage blocks inside a fused block. -/
def quadLowerBlock (d i : Nat) (hi : i + 1 < d)
    (g : Fin (2 ^ (d - (i + 1) - 1))) (b : Fin 2) : Fin (2 ^ (d - i - 1)) :=
  ⟨2 * g.val + b.val, by rw [quad_lower_blocks d i hi]; have := g.isLt; have := b.isLt; omega⟩

/-- Lower-stage pairs are the adjacent slabs inside a fused block. -/
theorem quadStageIndex_lower (d i lanes : Nat) (hi : i + 1 < d)
    (g : Fin (2 ^ (d - (i + 1) - 1))) (v : Fin (2 ^ i * lanes)) (s b : Fin 2) :
    stageIndex d ⟨i, by omega⟩ lanes (finProdFinEquiv (quadLowerBlock d i hi g s, v), b) =
      quadStageIndex d i lanes hi (finProdFinEquiv (g, v),
        ⟨b.val + 2 * s.val, by have := b.isLt; have := s.isLt; omega⟩) := by
  apply Fin.ext
  rw [stageIndex_block_val, quadStageIndex_val]
  simp only [quadLowerBlock, Fin.val_mk]
  ring

/-- Upper-stage pairs join the slabs separated by two strides. -/
theorem quadStageIndex_upper (d i lanes : Nat) (hi : i + 1 < d)
    (g : Fin (2 ^ (d - (i + 1) - 1))) (v : Fin (2 ^ i * lanes)) (s b : Fin 2) :
    stageIndex d ⟨i + 1, hi⟩ lanes (finProdFinEquiv (g,
      ⟨v.val + (2 ^ i * lanes) * s.val, by
        rw [pow_succ]; have := v.isLt; have := s.isLt; nlinarith⟩), b) =
      quadStageIndex d i lanes hi (finProdFinEquiv (g, v),
        ⟨s.val + 2 * b.val, by have := b.isLt; have := s.isLt; omega⟩) := by
  apply Fin.ext
  rw [stageIndex_block_val, quadStageIndex_val]
  simp only [Fin.val_mk, pow_succ]
  ring

/-- Read one side of a complete certified scalar stage. -/
theorem read_forwardStage_pair (p : Plan β d hd) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (g : Fin (2 ^ (d - i.val - 1))) (v : Fin (2 ^ i.val * lanes)) (b : Fin 2) :
    BF64.Packed.read (forwardStage p i lanes a)
      (stageIndex d i lanes (finProdFinEquiv (g, v), b)) =
      let out := forwardPair (p.get i g)
        (BF64.Packed.read a (stageIndex d i lanes (finProdFinEquiv (g, v), 0)))
        (BF64.Packed.read a (stageIndex d i lanes (finProdFinEquiv (g, v), 1)))
      if b = 0 then out.1 else out.2 := by
  rw [forwardStage_eq_sweep, read_sweep _ (stageIndex d i lanes).injective]
  have he : (finProdFinEquiv (g, v)).divNat = g :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (g, v))
  rw [he]

/-- An upper stage updates the separated slabs of each fused group. -/
theorem read_forwardStage_upper (p : Plan β d hd) (i lanes : Nat) (hi : i + 1 < d)
    (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (g : Fin (2 ^ (d - (i + 1) - 1))) (v : Fin (2 ^ i * lanes)) (s b : Fin 2) :
    BF64.Packed.read (forwardStage p ⟨i + 1, hi⟩ lanes a)
      (quadStageIndex d i lanes hi (finProdFinEquiv (g, v), finProdFinEquiv (b, s))) =
      let out := forwardPair (p.get ⟨i + 1, hi⟩ g)
        (BF64.Packed.read a (quadStageIndex d i lanes hi
          (finProdFinEquiv (g, v), finProdFinEquiv ((0 : Fin 2), s))))
        (BF64.Packed.read a (quadStageIndex d i lanes hi
          (finProdFinEquiv (g, v), finProdFinEquiv ((1 : Fin 2), s))))
      if b = 0 then out.1 else out.2 := by
  have hr := read_forwardStage_pair p ⟨i + 1, hi⟩ lanes a g
    ⟨v.val + (2 ^ i * lanes) * s.val, by
      rw [pow_succ]; have := v.isLt; have := s.isLt; nlinarith⟩ b
  rw [quadStageIndex_upper d i lanes hi g v s b,
    quadStageIndex_upper d i lanes hi g v s 0,
    quadStageIndex_upper d i lanes hi g v s 1] at hr
  exact hr

/-- A lower stage updates adjacent slabs of each fused group. -/
theorem read_forwardStage_lower (p : Plan β d hd) (i lanes : Nat) (hi : i + 1 < d)
    (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (g : Fin (2 ^ (d - (i + 1) - 1))) (v : Fin (2 ^ i * lanes)) (s b : Fin 2) :
    BF64.Packed.read (forwardStage p ⟨i, by omega⟩ lanes a)
      (quadStageIndex d i lanes hi (finProdFinEquiv (g, v), finProdFinEquiv (s, b))) =
      let out := forwardPair (p.get ⟨i, by omega⟩ (quadLowerBlock d i hi g s))
        (BF64.Packed.read a (quadStageIndex d i lanes hi
          (finProdFinEquiv (g, v), finProdFinEquiv (s, (0 : Fin 2)))))
        (BF64.Packed.read a (quadStageIndex d i lanes hi
          (finProdFinEquiv (g, v), finProdFinEquiv (s, (1 : Fin 2)))))
      if b = 0 then out.1 else out.2 := by
  have hr := read_forwardStage_pair p ⟨i, by omega⟩ lanes a
    (quadLowerBlock d i hi g s) v b
  rw [quadStageIndex_lower d i lanes hi g v s b,
    quadStageIndex_lower d i lanes hi g v s 0,
    quadStageIndex_lower d i lanes hi g v s 1] at hr
  exact hr

/-- Sweep two consecutive additive stages with one four-word load and store. -/
def forwardQuad (p : Plan β d hd) (i lanes : Nat) (hi : i + 1 < d)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  sweepQuad (quadStageIndex d i lanes hi) (fun j =>
    radix4 (p.get ⟨i + 1, hi⟩ j.divNat)
      (p.get ⟨i, by omega⟩ (quadLowerBlock d i hi j.divNat 0))
      (p.get ⟨i, by omega⟩ (quadLowerBlock d i hi j.divNat 1))) a

/-- A fused radix-four sweep is exactly two complete certified stages. -/
theorem forwardQuad_eq (p : Plan β d hd) (i lanes : Nat) (hi : i + 1 < d)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    forwardQuad p i lanes hi a =
      forwardStage p ⟨i, by omega⟩ lanes (forwardStage p ⟨i + 1, hi⟩ lanes a) := by
  apply BF64.Packed.read_ext
  intro j
  obtain ⟨⟨t, c⟩, rfl⟩ := (quadStageIndex d i lanes hi).surjective j
  obtain ⟨⟨g, v⟩, rfl⟩ := finProdFinEquiv.surjective t
  obtain ⟨⟨s, b⟩, rfl⟩ := (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).surjective c
  rw [forwardQuad, read_sweepQuad _ (quadStageIndex d i lanes hi).injective]
  have hdiv : (finProdFinEquiv (g, v)).divNat = g :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (g, v))
  simp only [hdiv]
  rw [read_forwardStage_lower, read_forwardStage_upper, read_forwardStage_upper]
  fin_cases s <;> fin_cases b <;> simp [radix4, Quad.get, finProdFinEquiv]

namespace Scalar
open AdditiveNTT.Bitsliced.Native

/-- Read and write four machine-addressed words around one register-level radix-four schedule. -/
@[inline] def butterfly4 (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (x0 x1 x2 x3 : USize) (h0 : x0.toNat < n) (h1 : x1.toNat < n)
    (h2 : x2.toNat < n) (h3 : x3.toNat < n) (t0 t1 t2 : Word) : BF64.Packed.Buffer n :=
  let v0 := read a hn x0 h0
  let v1 := read a hn x1 h1
  let v2 := read a hn x2 h2
  let v3 := read a hn x3 h3
  let u0 := v0 ^^^ (Word.mulMasked t0 ⟨v2⟩).val
  let u1 := v1 ^^^ (Word.mulMasked t0 ⟨v3⟩).val
  let u2 := u0 ^^^ v2
  let u3 := u1 ^^^ v3
  let y0 := u0 ^^^ (Word.mulMasked t1 ⟨u1⟩).val
  let y1 := y0 ^^^ u1
  let y2 := u2 ^^^ (Word.mulMasked t2 ⟨u3⟩).val
  let y3 := y2 ^^^ u3
  write (write (write (write a hn x0 h0 y0) hn x1 h1 y1) hn x2 h2 y2) hn x3 h3 y3

/-- Machine-addressed radix-four stores retain all four certified output words. -/
theorem butterfly4_eq (a : BF64.Packed.Buffer n) (hn : 8 * n < 4294967296)
    (x0 x1 x2 x3 : USize) (h0 : x0.toNat < n) (h1 : x1.toNat < n)
    (h2 : x2.toNat < n) (h3 : x3.toNat < n) (t0 t1 t2 : Word) :
    butterfly4 a hn x0 x1 x2 x3 h0 h1 h2 h3 t0 t1 t2 =
      let out := radix4 (Multiplier.masked t0) (Multiplier.masked t1) (Multiplier.masked t2)
        (BF64.Packed.read a ⟨x0.toNat, h0⟩) (BF64.Packed.read a ⟨x1.toNat, h1⟩)
        (BF64.Packed.read a ⟨x2.toNat, h2⟩) (BF64.Packed.read a ⟨x3.toNat, h3⟩)
      BF64.Packed.write (BF64.Packed.write (BF64.Packed.write
        (BF64.Packed.write a ⟨x0.toNat, h0⟩ out.1) ⟨x1.toNat, h1⟩ out.2.1)
        ⟨x2.toNat, h2⟩ out.2.2.1) ⟨x3.toNat, h3⟩ out.2.2.2 := by
  simp only [butterfly4, read_eq, write_eq, radix4, forwardPair, Multiplier.masked, Word.add]

/-- Fused radix-four sweeps retain only the byte array inside both machine loops. -/
def forwardQuadNative (p : Bitsliced.Plan β d hd) (i lanes : Nat) (hi : i + 1 < d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  let span := 2 ^ i * lanes
  let blocks := 2 ^ (d - (i + 1) - 1)
  have hcount : blocks * (4 * span) = 2 ^ d * lanes := quad_word_count d i lanes hi
  have hspos : 0 < span := Nat.mul_pos (by positivity) hlanes
  have hbpos : 0 < blocks := by positivity
  have hs : span < 4294967296 := by nlinarith
  have hb : blocks < 4294967296 := by nlinarith
  let stride := USize.ofNat span
  have hstride : stride.toNat = span := ofNat_toNat _ hs
  let quadStride := USize.ofNat (4 * span)
  have hquad : quadStride.toNat = 4 * span := ofNat_toNat _ (by nlinarith)
  pack <| foldSmall blocks hb (fun u hu a =>
    let g : Fin blocks := ⟨u.toNat, hu⟩
    let t0 := p.get ⟨i + 1, hi⟩ g
    let t1 := p.get ⟨i, by omega⟩ (quadLowerBlock d i hi g 0)
    let t2 := p.get ⟨i, by omega⟩ (quadLowerBlock d i hi g 1)
    let base := u * quadStride
    have hbase : base.toNat = u.toNat * (4 * span) := by
      rw [mul_toNat _ _ (by rw [hquad]; nlinarith), hquad]
    foldSmall span hs (fun v hv a =>
      let x0 := base + v
      let x1 := x0 + stride
      let x2 := x1 + stride
      let x3 := x2 + stride
      have hx0 : x0.toNat = u.toNat * (4 * span) + v.toNat := by
        rw [add_toNat _ _ (by rw [hbase]; nlinarith), hbase]
      have hx1 : x1.toNat = u.toNat * (4 * span) + v.toNat + span := by
        rw [add_toNat _ _ (by rw [hx0, hstride]; nlinarith), hx0, hstride]
      have hx2 : x2.toNat = u.toNat * (4 * span) + v.toNat + 2 * span := by
        rw [add_toNat _ _ (by rw [hx1, hstride]; nlinarith), hx1, hstride]
        omega
      have hx3 : x3.toNat = u.toNat * (4 * span) + v.toNat + 3 * span := by
        rw [add_toNat _ _ (by rw [hx2, hstride]; nlinarith), hx2, hstride]
        omega
      unpack (butterfly4 (pack a) hn x0 x1 x2 x3
        (by rw [hx0]; nlinarith) (by rw [hx1]; nlinarith)
        (by rw [hx2]; nlinarith) (by rw [hx3]; nlinarith) t0 t1 t2)) a) (unpack a)

/-- Specification-plan lookup recovers the compact masked multiplier. -/
theorem get_toPacked (p : Bitsliced.Plan β d hd) (i : Fin d) (u : Fin (2 ^ (d - i.val - 1))) :
    p.toPacked.get i u = Packed.Multiplier.masked (p.get i u) := by
  simp only [Bitsliced.Plan.toPacked, Packed.Plan.get, Vector.getElem_ofFn, Array.getElem_ofFn]

section
attribute [local irreducible] radix4 updateQuad Bitsliced.Plan.toPacked

/-- Machine radix-four sweeps preserve the complete certified four-word sweep. -/
theorem forwardQuadNative_eq (p : Bitsliced.Plan β d hd) (i lanes : Nat) (hi : i + 1 < d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    forwardQuadNative p i lanes hi hlanes a hn = forwardQuad p.toPacked i lanes hi a := by
  unfold forwardQuadNative forwardQuad sweepQuad
  rw [foldSmall_pack, pack_unpack, foldl_blocks]
  rw [foldSmall_eq]
  congr 1
  funext a g
  rw [foldSmall_pack]
  simp only [pack_unpack, foldSmall_eq]
  congr 1
  funext a v
  change _ = updateQuad (quadStageIndex d i lanes hi) (fun j =>
    radix4 (p.toPacked.get ⟨i + 1, hi⟩ j.divNat)
      (p.toPacked.get ⟨i, by omega⟩ (quadLowerBlock d i hi j.divNat 0))
      (p.toPacked.get ⟨i, by omega⟩ (quadLowerBlock d i hi j.divNat 1))) a
        (finProdFinEquiv (g, v))
  have hdiv : (finProdFinEquiv (g, v)).divNat = g :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (g, v))
  have hcount := quad_word_count d i lanes hi
  have hg := g.isLt
  have hv := v.isLt
  have hspos : 0 < 2 ^ i * lanes := Nat.mul_pos (by positivity) hlanes
  have hbpos : 0 < 2 ^ (d - (i + 1) - 1) := by positivity
  have hs : 2 ^ i * lanes < 4294967296 := by nlinarith
  have hgn : g.val < 4294967296 := by nlinarith
  have h0 : g.val * (4 * (2 ^ i * lanes)) + v.val < 4294967296 := by nlinarith
  have h1 : g.val * (4 * (2 ^ i * lanes)) + v.val + (2 ^ i * lanes) <
      4294967296 := by nlinarith
  have h2 : g.val * (4 * (2 ^ i * lanes)) + v.val + (2 ^ i * lanes) +
      (2 ^ i * lanes) < 4294967296 := by nlinarith
  have h3 : g.val * (4 * (2 ^ i * lanes)) + v.val + (2 ^ i * lanes) +
      (2 ^ i * lanes) + (2 ^ i * lanes) < 4294967296 := by nlinarith
  simp only [butterfly4_eq, ← USize.ofNat_add, ← USize.ofNat_mul,
    ofNat_toNat _ h0, ofNat_toNat _ h1, ofNat_toNat _ h2, ofNat_toNat _ h3,
    ofNat_toNat _ hgn, updateQuad, hdiv, get_toPacked]
  have hindex (side : Fin 4) :
      quadStageIndex d i lanes hi (finProdFinEquiv (g, v), side) =
        ⟨g.val * (4 * (2 ^ i * lanes)) + v.val + side.val * (2 ^ i * lanes), by
          have := side.isLt; nlinarith⟩ := by
    apply Fin.ext
    rw [quadStageIndex_val]
    ring
  simp only [hindex, Fin.val_zero, Fin.val_one,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl,
    Nat.succ_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc]

end

/-- Removing the highest stage leaves the same descending transform prefix. -/
theorem forward_succ (p : Bitsliced.Plan β d hd) (ell : Nat) (hell : ell + 1 ≤ d)
    (lanes : Nat) (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    forward p (ell + 1) hell lanes hlanes a hn =
      forward p ell (by omega) lanes hlanes
        (forwardStage p ⟨ell, by omega⟩ lanes hlanes a hn) hn := by
  unfold forward
  rw [Fin.foldl_succ]
  simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel]
  congr 1
  funext a k
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

/-- Descending radix-four sweeps, with a single radix-two stage for odd prefixes. -/
def forwardFused (p : Bitsliced.Plan β d hd) (ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  match ell with
  | 0 => a
  | 1 => forwardStage p ⟨0, by omega⟩ lanes hlanes a hn
  | k + 2 => forwardFused p k (by omega) lanes hlanes
      (forwardQuadNative p k lanes (by omega) hlanes a hn) hn

/-- Fused machine sweeps preserve every certified transform prefix. -/
@[csimp] theorem forwardFused_code : @forward = @forwardFused := by
  funext β d hd p ell hell lanes hlanes a hn
  induction ell using Nat.twoStepInduction generalizing a with
  | zero => rfl
  | one =>
    rw [forwardFused, forward_succ p 0 (by omega)]
    rfl
  | more k ih _ =>
    rw [forwardFused, forward_succ p (k + 1) hell, forward_succ p k (by omega)]
    rw [← ih (by omega)]
    congr 1
    rw [forwardQuadNative_eq, forwardQuad_eq, forwardStage_eq, forwardStage_eq]

end Scalar

end AdditiveNTT.Packed
