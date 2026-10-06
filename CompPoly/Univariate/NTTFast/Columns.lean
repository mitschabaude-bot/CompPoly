/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Parallel
public import CompPoly.Univariate.NTTFast.Reverse32

/-! # Column-parallel natural-order transform on field arrays

A transform of `2 ^ logN` coefficients is viewed as sixteen rows of `M = 2 ^ (logN - 4)`
columns. Its top four layers act independently on every column, so `S` column tasks each
copy their column range of the sixteen rows into a local buffer and run the two top
radix-four passes there, with the matching twiddle columns. Leaf task `l` collects row `l`
from every column task, runs the remaining passes and reverses its own bit order, with
optional scaling. One sequential pass interleaves the sixteen leaves into natural order.

Every coefficient crosses task boundaries twice: arrays of boxed values are marked for
sharing element by element, so the design minimizes such crossings. No externs are used.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Columns

variable {α R : Type*}

/-- Copy entries `k, …, cnt - 1` of a range of `src` into a range of `dst`. -/
def copyGo (src : @& Array α) (si di cnt k : USize) (dst : Array α)
    (_hk : k ≤ cnt) (hs : si.toNat + cnt.toNat ≤ src.size) (hd : di.toNat + cnt.toNat ≤ dst.size)
    (hu : src.size < USize.size ∧ dst.size < USize.size) : Array α :=
  if hlt : k < cnt then
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    have hkn : k.toNat < cnt.toNat := hlt
    have hcs := cnt.toNat_lt_size
    have hds := di.toNat_lt_size
    have ha : (si + k).toNat = si.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hb : (di + k).toNat = di.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hk1 : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by omega)
    copyGo src si di cnt (k + 1) (dst.uset (di + k) (src.uget (si + k) (by omega)) (by omega))
      (by rw [USize.le_iff_toNat_le, hk1]; omega) hs
      (by simp only [Array.size_uset]; exact hd) (by simp only [Array.size_uset]; exact hu)
  else dst
termination_by cnt.toNat - k.toNat
decreasing_by
  have : k.toNat < cnt.toNat := hlt
  have : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by
    have := cnt.toNat_lt_size; omega)
  omega

/-- Copy `cnt` entries of `src` from `si` into `dst` from `di`; out-of-range copies do nothing. -/
def copyRange (src : @& Array α) (si : Nat) (dst : Array α) (di cnt : Nat) : Array α :=
  if h : si + cnt ≤ src.size ∧ di + cnt ≤ dst.size ∧ src.size < USize.size ∧
      dst.size < USize.size then
    copyGo src (USize.ofNatLT si (by omega)) (USize.ofNatLT di (by omega))
      (USize.ofNatLT cnt (by omega)) 0 dst (by simp only [USize.zero_le])
      (by simp only [USize.toNat_ofNatLT]; omega) (by simp only [USize.toNat_ofNatLT]; omega)
      ⟨h.2.2.1, h.2.2.2⟩
  else dst

/-- Rows `0, …, r - 1` of a matrix with rows of length `M`, restricted to the columns
`j0, …, j0 + cs - 1`, as a row-major `r × cs` array. -/
def gatherRows [Zero α] (src : @& Array α) (M j0 cs r : Nat) : Array α :=
  (List.range r).foldl (fun acc k ↦ copyRange src (k * M + j0) acc (k * cs) cs)
    (Array.replicate (r * cs) 0)

/-- The top two radix-four passes of a `16 × M` transform on columns `j0, …, j0 + cs - 1`. -/
@[specialize] def columnTask [Field R] [DecidableEq R] (x : @& Array R)
    (tw : @& Array (Array R)) (logN M cs j0 : Nat) : Array R :=
  let a := gatherRows x M j0 cs 16
  let a := Plan.stageBlocksDIF (gatherRows (tw.getD (logN - 1) #[]) M j0 cs 8)
    (gatherRows (tw.getD (logN - 2) #[]) M j0 cs 4) (16 * cs) (4 * cs) 1 0 a
  Plan.stageBlocksDIF (gatherRows (tw.getD (logN - 3) #[]) M j0 cs 2)
    (gatherRows (tw.getD (logN - 4) #[]) M j0 cs 1) (4 * cs) cs 4 0 a

/-- Row `l` of every column result, in column order. -/
def gatherLeaf [Zero α] (cols : @& Array (Array α)) (cs l : Nat) : Array α :=
  (List.range cols.size).foldl (fun acc s ↦ copyRange (cols.getD s #[]) (l * cs) acc (s * cs) cs)
    (Array.replicate (cols.size * cs) 0)

/-- Store entries `q, …, M - 1` of the bit-reversed `a`, optionally scaled by `f`. -/
def reverseGo [Mul α] (a : @& Array α) (shift : UInt32) (scale : Bool) (f : α) (M q : USize)
    (out : Array α) : Array α :=
  if hq : q < M then
    have hM := M.toNat_lt_size
    have hq1 : (q + 1).toNat = q.toNat + 1 := Plan.usize_add_one q (by
      have : q.toNat < M.toNat := hq
      omega)
    let j := (reverse32 q.toUInt32 >>> shift).toUSize
    if h : j.toNat < a.size ∧ q.toNat < out.size then
      let v := a.uget j h.1
      reverseGo a shift scale f M (q + 1) (out.uset q (if scale then f * v else v) h.2)
    else out
  else out
termination_by M.toNat - q.toNat
decreasing_by
  have : q.toNat < M.toNat := hq
  omega

/-- A `2 ^ m`-entry array in bit-reversed order, optionally scaled by `f`. -/
def reverseLeaf [Zero α] [Mul α] (m : Nat) (scale : Bool) (f : α) (a : @& Array α) :
    Array α :=
  reverseGo a (32 - m).toUInt32 scale f (2 ^ m).toUSize 0 (Array.replicate (2 ^ m) 0)

/-- Leaf `l`: collect its row, run the remaining passes and reverse its bit order. -/
@[specialize] def leafTask [Field R] [DecidableEq R] (cols : @& Array (Array R))
    (tw : @& Array (Array R)) (rest : List Nat) (m cs l : Nat) (scale : Bool) (f : R) :
    Array R :=
  reverseLeaf m scale f (Parallel.runPasses false tw rest (gatherLeaf cols cs l))

/-- Store natural-order entries `16 * q + c` from the reversed leaves, for `q` from `q`
to `M - 1`. Entry `16 * q + c` is entry `q` of leaf `bitrev₄ c`. -/
def assembleGo [Zero α] (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : @& Array α)
    (q M : Nat) (out : Array α) : Array α :=
  if q < M then
    let out := out.set! (16 * q) (l0.getD q 0)
    let out := out.set! (16 * q + 1) (l8.getD q 0)
    let out := out.set! (16 * q + 2) (l4.getD q 0)
    let out := out.set! (16 * q + 3) (l12.getD q 0)
    let out := out.set! (16 * q + 4) (l2.getD q 0)
    let out := out.set! (16 * q + 5) (l10.getD q 0)
    let out := out.set! (16 * q + 6) (l6.getD q 0)
    let out := out.set! (16 * q + 7) (l14.getD q 0)
    let out := out.set! (16 * q + 8) (l1.getD q 0)
    let out := out.set! (16 * q + 9) (l9.getD q 0)
    let out := out.set! (16 * q + 10) (l5.getD q 0)
    let out := out.set! (16 * q + 11) (l13.getD q 0)
    let out := out.set! (16 * q + 12) (l3.getD q 0)
    let out := out.set! (16 * q + 13) (l11.getD q 0)
    let out := out.set! (16 * q + 14) (l7.getD q 0)
    let out := out.set! (16 * q + 15) (l15.getD q 0)
    assembleGo l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 (q + 1) M out
  else out
termination_by M - q

/-- Interleave sixteen reversed `M`-entry leaves into natural order. -/
def assemble [Zero α] (r : @& Array (Array α)) (M : Nat) : Array α :=
  assembleGo (r.getD 0 #[]) (r.getD 1 #[]) (r.getD 2 #[]) (r.getD 3 #[]) (r.getD 4 #[])
    (r.getD 5 #[]) (r.getD 6 #[]) (r.getD 7 #[]) (r.getD 8 #[]) (r.getD 9 #[]) (r.getD 10 #[])
    (r.getD 11 #[]) (r.getD 12 #[]) (r.getD 13 #[]) (r.getD 14 #[]) (r.getD 15 #[]) 0 M
    (Array.replicate (16 * M) 0)

/-- Wait for every task without blocking a worker; results keep the task order. -/
def joinTasks (ts : Array (Task α)) : Task (Array α) :=
  ts.foldl (fun acc t ↦ acc.bind (sync := true) fun xs ↦ t.map (sync := true) fun x ↦ xs.push x)
    (.pure #[])

/-- The complete column-parallel transform: natural-order input, natural-order output,
optionally scaled by `f`; `rest` are the passes of a `2 ^ (logN - 4)`-entry leaf. -/
@[specialize] def transform [Field R] [DecidableEq R] (tw : Array (Array R)) (logN S : Nat)
    (rest : List Nat) (scale : Bool) (f : R) (x : Array R) : Array R :=
  let M := 2 ^ (logN - 4)
  let cs := M / S
  let cols := (Array.range S).map fun s ↦ Task.spawn fun _ ↦ columnTask x tw logN M cs (s * cs)
  let all := joinTasks cols
  let leaves := (Array.range 16).map fun l ↦ all.bind fun cols ↦ Task.spawn fun _ ↦
    leafTask cols tw rest (logN - 4) cs l scale f
  assemble (leaves.map Task.get) M

end CompPoly.CPolynomial.NTTFast.Columns
