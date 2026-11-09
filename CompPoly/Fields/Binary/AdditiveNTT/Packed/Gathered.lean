/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Window

/-! # Parallel gathered far passes over bounded cache scratch -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace AdditiveNTT.Packed.Gathered
open BF64 Window

/-- Power-of-two chunks exactly cover each far-stage slab. -/
theorem span_count (i chunk lanes : Nat) (hchunk : chunk ≤ i) :
    2 ^ (i - chunk) * (2 ^ chunk * lanes) = 2 ^ i * lanes := window_count i chunk lanes hchunk

/-- Gather four strided slabs into adjacent scratch rows. -/
def gather (d i chunk lanes : Nat) (hi : i + 1 < d) (hchunk : chunk ≤ i)
    (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (g : Fin (2 ^ (d - (i + 1) - 1))) (c : Fin (2 ^ (i - chunk))) :
    BF64.Packed.Buffer (4 * (2 ^ chunk * lanes)) :=
  join (Vector.ofFn fun side : Fin 4 =>
    slice a (g.val * (4 * (2 ^ i * lanes)) + side.val * (2 ^ i * lanes) +
      c.val * (2 ^ chunk * lanes)) (2 ^ chunk * lanes) (by
        have hc := span_count i chunk lanes hchunk
        have hd := quad_word_count d i lanes hi
        have hg := g.isLt; have hs := side.isLt; have hj := c.isLt
        have hmul := Nat.mul_le_mul_right (2 ^ chunk * lanes) (Nat.succ_le_of_lt hj)
        rw [Nat.succ_mul, hc] at hmul
        have hsMul := Nat.mul_le_mul_right (2 ^ i * lanes) (Nat.succ_le_of_lt hs)
        have hgMul := Nat.mul_le_mul_right (4 * (2 ^ i * lanes)) (Nat.succ_le_of_lt hg)
        calc
          _ ≤ g.val * (4 * (2 ^ i * lanes)) + side.val * (2 ^ i * lanes) +
              2 ^ i * lanes := by omega
          _ = g.val * (4 * (2 ^ i * lanes)) + (side.val + 1) * (2 ^ i * lanes) := by ring
          _ ≤ g.val * (4 * (2 ^ i * lanes)) + 4 * (2 ^ i * lanes) := Nat.add_le_add_left hsMul _
          _ = (g.val + 1) * (4 * (2 ^ i * lanes)) := by ring
          _ ≤ _ := by rwa [hd] at hgMul))

/-- A two-stage scratch plan retains the global far block's three twiddles. -/
def twiddles (p : Twiddles d) (i : Nat) (hi : i + 1 < d)
    (g : Fin (2 ^ (d - (i + 1) - 1))) : Twiddles 2 :=
  fun j u => if h : j.val = 1 then p ⟨i + 1, hi⟩ g
    else p ⟨i, by omega⟩ (quadLowerBlock d i hi g ⟨u.val, by
      have hj : j.val = 0 := by have := j.isLt; omega
      have hu := u.isLt
      simp only [hj, Nat.sub_zero, Nat.reduceSub, Nat.reducePow] at hu
      exact hu⟩)

/-- Gathered radix-four tasks own their scratch through every butterfly. -/
def tasks (p : Twiddles d) (i chunk lanes : Nat) (hi : i + 1 < d) (hchunk : chunk ≤ i)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    Vector (BF64.Packed.Buffer (4 * (2 ^ chunk * lanes)))
      (2 ^ (d - (i + 1) - 1) * 2 ^ (i - chunk)) :=
  let jobs := Vector.ofFn fun task : Fin (2 ^ (d - (i + 1) - 1) * 2 ^ (i - chunk)) =>
    Task.spawn fun _ =>
      let coordinate := finProdFinEquiv.symm task
      Window.quadNative (twiddles p i hi coordinate.1) 0 (2 ^ chunk * lanes) (by decide)
        (by positivity) (gather d i chunk lanes hi hchunk a coordinate.1 coordinate.2) (by
          have hc := span_count i chunk lanes hchunk
          have hd := quad_word_count d i lanes hi
          have hp : 0 < 2 ^ (i - chunk) := by positivity
          have hg : 0 < 2 ^ (d - (i + 1) - 1) := by positivity
          have hw : 2 ^ chunk * lanes ≤ 2 ^ i * lanes := by
            simpa only [hc] using Nat.le_mul_of_pos_left (2 ^ chunk * lanes) hp
          have hs : 4 * (2 ^ i * lanes) ≤ 2 ^ d * lanes := by
            simpa only [hd] using Nat.le_mul_of_pos_left (4 * (2 ^ i * lanes)) hg
          have hsmall := le_trans (Nat.mul_le_mul_left 4 hw) hs
          exact lt_of_le_of_lt
            (by simpa only [Nat.reducePow] using Nat.mul_le_mul_left 8 hsmall) hn)
  jobs.map Task.get

/-- Scatter completed scratch slabs in their original contiguous output order. -/
def scatter (d i chunk lanes : Nat) (hi : i + 1 < d) (hchunk : chunk ≤ i)
    (results : Vector (BF64.Packed.Buffer (4 * (2 ^ chunk * lanes)))
      (2 ^ (d - (i + 1) - 1) * 2 ^ (i - chunk))) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  let slabs := Vector.ofFn fun j : Fin ((2 ^ (d - (i + 1) - 1) * 4) * 2 ^ (i - chunk)) =>
    let coordinate := finProdFinEquiv.symm j
    let blockSide := finProdFinEquiv.symm coordinate.1
    let task := finProdFinEquiv (blockSide.1, coordinate.2)
    slice results[task.val] (blockSide.2.val * (2 ^ chunk * lanes)) (2 ^ chunk * lanes)
      (by
        have h := Nat.mul_le_mul_right (2 ^ chunk * lanes) (Nat.succ_le_of_lt blockSide.2.isLt)
        simpa only [Nat.succ_mul] using h)
  let out := join slabs
  ⟨out.val, out.property.trans (by
    have hc := span_count i chunk lanes hchunk
    have hd := quad_word_count d i lanes hi
    calc
      _ = 2 ^ (d - (i + 1) - 1) * (4 * (2 ^ (i - chunk) * (2 ^ chunk * lanes))) := by ring
      _ = _ := by rw [hc, hd])⟩

/-- One far pass gathers, executes fused butterflies, and scatters each cache-sized task. -/
def quad (p : Twiddles d) (i chunk lanes : Nat) (hi : i + 1 < d) (hchunk : chunk ≤ i)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  scatter d i chunk lanes hi hchunk (tasks p i chunk lanes hi hchunk hlanes a hn)

/-- The original column coordinate of a word in a gathered chunk. -/
def column (i chunk lanes : Nat) (hchunk : chunk ≤ i) (c : Fin (2 ^ (i - chunk)))
    (v : Fin (2 ^ chunk * lanes)) : Fin (2 ^ i * lanes) :=
  Fin.cast (span_count i chunk lanes hchunk) (finProdFinEquiv (c, v))

/-- Four adjacent scratch rows preserve the global strided butterfly addresses. -/
theorem read_gather (d i chunk lanes : Nat) (hi : i + 1 < d) (hchunk : chunk ≤ i)
    (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (g : Fin (2 ^ (d - (i + 1) - 1))) (c : Fin (2 ^ (i - chunk)))
    (v : Fin (2 ^ chunk * lanes)) (side : Fin 4) :
    BF64.Packed.read (gather d i chunk lanes hi hchunk a g c) (finProdFinEquiv (side, v)) =
      BF64.Packed.read a (quadStageIndex d i lanes hi
        (finProdFinEquiv (g, column i chunk lanes hchunk c v), side)) := by
  rw [gather, read_join, Vector.getElem_ofFn, read_slice]
  congr 1
  apply Fin.ext
  rw [quadStageIndex_val]
  simp only [column, Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk]
  ring

/-- The single-block scratch sweep uses adjacent row coordinates. -/
theorem scratch_index (width : Nat) (v : Fin width) (side : Fin 4) :
    quadStageIndex 2 0 width (by decide) (finProdFinEquiv ((0 : Fin 1),
      ⟨v.val, by simpa only [Nat.pow_zero, Nat.one_mul] using v.isLt⟩), side) =
      finProdFinEquiv (side, v) := by
  apply Fin.ext
  rw [quadStageIndex_val]
  simp only [Nat.pow_zero, Nat.one_mul, Fin.val_zero, Nat.mul_zero, Nat.add_zero,
    finProdFinEquiv, Equiv.coe_fn_mk]

attribute [local irreducible] radix4

/-- Each gathered task computes the exact global four-word butterfly for its chunk. -/
theorem read_tasks (p : Twiddles d) (i chunk lanes : Nat) (hi : i + 1 < d) (hchunk : chunk ≤ i)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (g : Fin (2 ^ (d - (i + 1) - 1))) (c : Fin (2 ^ (i - chunk)))
    (v : Fin (2 ^ chunk * lanes)) (side : Fin 4) :
    BF64.Packed.read (tasks p i chunk lanes hi hchunk hlanes a hn)[(finProdFinEquiv (g, c)).val]
      (finProdFinEquiv (side, v)) =
      (radix4 (Multiplier.masked (p ⟨i + 1, hi⟩ g))
        (Multiplier.masked (p ⟨i, by omega⟩ (quadLowerBlock d i hi g 0)))
        (Multiplier.masked (p ⟨i, by omega⟩ (quadLowerBlock d i hi g 1)))
        (BF64.Packed.read a (quadStageIndex d i lanes hi
          (finProdFinEquiv (g, column i chunk lanes hchunk c v), 0)))
        (BF64.Packed.read a (quadStageIndex d i lanes hi
          (finProdFinEquiv (g, column i chunk lanes hchunk c v), 1)))
        (BF64.Packed.read a (quadStageIndex d i lanes hi
          (finProdFinEquiv (g, column i chunk lanes hchunk c v), 2)))
        (BF64.Packed.read a (quadStageIndex d i lanes hi
          (finProdFinEquiv (g, column i chunk lanes hchunk c v), 3)))).get side := by
  simp only [tasks, Vector.getElem_map, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
  change BF64.Packed.read (Window.quadNative (twiddles p i hi g) 0 (2 ^ chunk * lanes)
    (by decide) (by positivity) (gather d i chunk lanes hi hchunk a g c) _) _ = _
  rw [Window.quadNative_eq, Window.quad, ← scratch_index, read_sweepQuad _
    (quadStageIndex 2 0 (2 ^ chunk * lanes) (by decide)).injective]
  simp only [scratch_index, read_gather]
  simp only [twiddles, Fin.val_one, Fin.val_zero, dite_true, dite_false, Nat.zero_ne_one,
    quadLowerBlock, Fin.val_mk, Fin.divNat, finProdFinEquiv, Equiv.coe_fn_mk,
    Nat.pow_zero, Nat.one_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
    Nat.div_eq_of_lt v.isLt]

/-- Scattered slabs have the original full-domain word count. -/
theorem scatter_count (d i chunk lanes : Nat) (hi : i + 1 < d) (hchunk : chunk ≤ i) :
    ((2 ^ (d - (i + 1) - 1) * 4) * 2 ^ (i - chunk)) * (2 ^ chunk * lanes) = 2 ^ d * lanes := by
  calc
    _ = 2 ^ (d - (i + 1) - 1) * (4 * (2 ^ (i - chunk) * (2 ^ chunk * lanes))) := by ring
    _ = _ := by rw [span_count i chunk lanes hchunk, quad_word_count d i lanes hi]

/-- Scatter preserves each task, slab, and local word coordinate. -/
theorem read_scatter (d i chunk lanes : Nat) (hi : i + 1 < d) (hchunk : chunk ≤ i)
    (results : Vector (BF64.Packed.Buffer (4 * (2 ^ chunk * lanes)))
      (2 ^ (d - (i + 1) - 1) * 2 ^ (i - chunk)))
    (g : Fin (2 ^ (d - (i + 1) - 1))) (c : Fin (2 ^ (i - chunk)))
    (v : Fin (2 ^ chunk * lanes)) (side : Fin 4) :
    BF64.Packed.read (scatter d i chunk lanes hi hchunk results)
      (quadStageIndex d i lanes hi (finProdFinEquiv (g, column i chunk lanes hchunk c v), side)) =
      BF64.Packed.read results[(finProdFinEquiv (g, c)).val] (finProdFinEquiv (side, v)) := by
  have hbound : (quadStageIndex d i lanes hi
      (finProdFinEquiv (g, column i chunk lanes hchunk c v), side)).val <
      ((2 ^ (d - (i + 1) - 1) * 4) * 2 ^ (i - chunk)) * (2 ^ chunk * lanes) := by
    rw [scatter_count d i chunk lanes hi hchunk]
    exact (quadStageIndex d i lanes hi
      (finProdFinEquiv (g, column i chunk lanes hchunk c v), side)).isLt
  dsimp only [scatter]
  change BF64.Packed.read (join _) ⟨(quadStageIndex d i lanes hi
    (finProdFinEquiv (g, column i chunk lanes hchunk c v), side)).val, hbound⟩ = _
  have he : (⟨(quadStageIndex d i lanes hi
      (finProdFinEquiv (g, column i chunk lanes hchunk c v), side)).val, hbound⟩ :
      Fin (((2 ^ (d - (i + 1) - 1) * 4) * 2 ^ (i - chunk)) * (2 ^ chunk * lanes))) =
      finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (g, side), c), v) := by
    apply Fin.ext
    rw [quadStageIndex_val]
    simp only [column, Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk]
    have hc := span_count i chunk lanes hchunk
    calc
      _ = v.val + (2 ^ chunk * lanes) * c.val + (2 ^ i * lanes) * (side.val + 4 * g.val) := rfl
      _ = v.val + (2 ^ chunk * lanes) * c.val +
          (2 ^ (i - chunk) * (2 ^ chunk * lanes)) * (side.val + 4 * g.val) := by rw [hc]
      _ = _ := by ring
  rw [he, read_join, Vector.getElem_ofFn]
  simp only [Fin.eta, Equiv.symm_apply_apply]
  rw [read_slice]
  congr 1
  apply Fin.ext
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  ring

/-- Gathered tasks preserve every output of the full-domain fused sweep. -/
theorem quad_eq (p : Twiddles d) (i chunk lanes : Nat) (hi : i + 1 < d) (hchunk : chunk ≤ i)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    quad p i chunk lanes hi hchunk hlanes a hn = Window.quad p i lanes hi a := by
  apply BF64.Packed.read_ext
  intro j
  obtain ⟨⟨t, side⟩, rfl⟩ := (quadStageIndex d i lanes hi).surjective j
  obtain ⟨⟨g, col⟩, rfl⟩ := finProdFinEquiv.surjective t
  obtain ⟨⟨c, v⟩, he⟩ := finProdFinEquiv.surjective
    (Fin.cast (span_count i chunk lanes hchunk).symm col)
  have hcol : column i chunk lanes hchunk c v = col := by
    apply Fin.ext
    have hv := congrArg (fun x : Fin (2 ^ (i - chunk) * (2 ^ chunk * lanes)) => x.val) he
    simpa only [column, Fin.val_cast] using hv
  subst col
  rw [quad, read_scatter, read_tasks, Window.quad,
    read_sweepQuad _ (quadStageIndex d i lanes hi).injective]
  have hdiv : (finProdFinEquiv (g, column i chunk lanes hchunk c v)).divNat = g :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (g, column i chunk lanes hchunk c v))
  simp only [hdiv]


/-- L2-sized gathered scratch, containing four complete slabs of each chunk. -/
def chunkDepth (i lanes : Nat) : Nat := min i (Nat.log2 (max (131072 / lanes) 1) - 2)

/-- Gathered far stages stop at the deep-pass boundary. -/
def far (p : Twiddles d) (near : Nat) (ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  match ell with
  | 0 => a
  | 1 => if near = 0 then stageNative p ⟨0, by omega⟩ lanes hlanes a hn else a
  | k + 2 =>
    if near ≤ k then
      far p near k (by omega) lanes hlanes
        (quad p k (chunkDepth k lanes) lanes (by omega) (Nat.min_le_left ..) hlanes a hn) hn
    else if near = k + 1 then stageNative p ⟨k + 1, by omega⟩ lanes hlanes a hn else a

/-- Gathered passes retain the exact far-stage order and twiddles. -/
theorem far_eq (p : Twiddles d) (near ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    far p near ell hell lanes hlanes a hn = Window.farSpec p near ell hell lanes a := by
  induction ell using Nat.twoStepInduction generalizing a with
  | zero => rfl
  | one =>
    simp only [far, farSpec]
    by_cases h : near = 0
    · simp only [h, le_refl, ite_true, stageNative_eq]
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  | more k ih _ =>
    rw [far]
    by_cases h : near ≤ k
    · rw [ite_eq_left h, ih (by omega), quad_eq, Window.quad_eq, farSpec,
        ite_eq_left (by omega), farSpec, ite_eq_left h]
    · rw [ite_eq_right h, farSpec]
      by_cases he : near = k + 1
      · rw [ite_eq_left he, ite_eq_left (by omega), farSpec, ite_eq_right h, stageNative_eq]
      · rw [ite_eq_right he, ite_eq_right (by omega)]

/-- Parallel far/deep execution with a sink on each completed near window. -/
def run {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - nearDepth workers d ell lanes)) →
      BF64.Packed.Buffer (2 ^ nearDepth workers d ell lanes * lanes) → α) :=
  deep workers p (nearDepth workers d ell lanes) lanes
    (le_trans (nearDepth_le ..) hell) hlanes
    (far p (nearDepth workers d ell lanes) ell hell lanes hlanes a hn) hn sink

/-- Parallel gathered and deep execution refines the exact global-window specification. -/
theorem run_eq {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - nearDepth workers d ell lanes)) →
      BF64.Packed.Buffer (2 ^ nearDepth workers d ell lanes * lanes) → α) :
    run workers p ell lanes hell hlanes a hn sink =
      Window.run workers p ell lanes hell hlanes a hn sink := by
  rw [run, Window.run, far_eq, Window.far_eq]

/-- Parallel gathered/deep execution with a consumer-owned joined codeword. -/
def runJoined {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - nearDepth workers d ell lanes)) →
      BF64.Packed.Buffer (2 ^ nearDepth workers d ell lanes * lanes) → α) :=
  let result := run workers p ell lanes hell hlanes a hn sink
  (joinDomain d (nearDepth workers d ell lanes) lanes (le_trans (nearDepth_le ..) hell)
    (result.map Prod.fst), result.map Prod.snd)

/-- Gathered execution preserves the full-domain transform and every row-sink output. -/
theorem runJoined_eq {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - nearDepth workers d ell lanes)) →
      BF64.Packed.Buffer (2 ^ nearDepth workers d ell lanes * lanes) → α) :
    runJoined workers p ell lanes hell hlanes a hn sink =
      Window.runJoined workers p ell lanes hell hlanes a hn sink := by
  simp only [runJoined, run_eq, Window.runJoined]

/-- Complete gathered/deep scalar execution without an authentication sink. -/
def forward (workers : Nat) (p : Bitsliced.Plan β d hd) (ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  (runJoined workers (fun i g => p.get i g) ell lanes hell hlanes a hn (fun _ _ => ())).1

/-- Parallel far/deep sweeps preserve every byte of the certified scalar transform. -/
theorem forward_code (workers : Nat) : @Scalar.forwardFused β d hd = @forward β d hd workers := by
  funext p ell hell lanes hlanes a hn
  rw [← Scalar.forwardFused_code, Scalar.forward_eq]
  simp only [forward, runJoined_eq, Window.runJoined_eq, Window.forwardSpec_toPacked]

end AdditiveNTT.Packed.Gathered
