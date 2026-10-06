/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Parallel
public import CompPoly.Univariate.NTTFast.Reverse32
public import CompPoly.Data.Bytes.Words

/-! # Column-parallel natural-order transform on field arrays

A transform of `2 ^ logN` coefficients is viewed as sixteen rows of `M = 2 ^ (logN - 4)`
columns. Its top four layers act independently on every column, so `S` column tasks each
copy their column range of the sixteen rows into a local buffer and run the two top
radix-four passes there, with the matching twiddle columns. Leaf task `l` collects row `l`
from every column task, runs the remaining passes and reverses its own bit order, with
optional scaling. One sequential pass interleaves the sixteen leaves into natural order.

Every coefficient crosses task boundaries twice. The runtime marks an array of boxed values for
sharing element by element, under the task manager's lock, when a task returns it; so tasks
return their results as raw 32-bit words in a `ByteArray` (`Word32Repr`), which is marked at
once. Leaf `l` stores its words after `16 l` padding words, so that the final pass, which reads
all sixteen leaves at the same position, does not map them to the same cache sets. No externs
are used.
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

open ByteWords in
/-- Store entries `k, …, cnt - 1` of `src` as words `off + k, …` of `dst`. -/
def encodeGo [Word32Repr α] (src : @& Array α) (off cnt k : USize) (dst : ByteArray)
    (_hk : k ≤ cnt) (hs : cnt.toNat ≤ src.size) (hd : 4 * (off.toNat + cnt.toNat) ≤ dst.size)
    (hu : dst.size < USize.size) : ByteArray :=
  if hlt : k < cnt then
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    have hkn : k.toNat < cnt.toNat := hlt
    have ha : (off + k).toNat = off.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hk1 : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by
      have := cnt.toNat_lt_size; omega)
    encodeGo src off cnt (k + 1)
      (writeWordU dst (off + k) (Word32Repr.toWord (src.uget k (by omega))) (by omega) hu)
      (by rw [USize.le_iff_toNat_le, hk1]; omega) hs
      (by simp only [size_writeWordU]; exact hd) (by simp only [size_writeWordU]; exact hu)
  else dst
termination_by cnt.toNat - k.toNat
decreasing_by
  have : k.toNat < cnt.toNat := hlt
  have : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by
    have := cnt.toNat_lt_size; omega)
  omega

/-- The entries of `a` as words, after `off` padding words. -/
def encode [Word32Repr α] (a : @& Array α) (off : Nat) : ByteArray :=
  let dst := ByteWords.buffer (4 * (off + a.size))
  if h : 4 * (off + a.size) < USize.size then
    encodeGo a (USize.ofNatLT off (by omega)) (USize.ofNatLT a.size (by omega)) 0 dst
      (by simp only [USize.zero_le]) (by simp only [USize.toNat_ofNatLT]; omega)
      (by simp only [USize.toNat_ofNatLT, dst, ByteWords.size_buffer]; omega)
      (by simp only [dst, ByteWords.size_buffer]; exact h)
  else dst

open ByteWords in
/-- Decode words `si + k, …, si + cnt - 1` of `src` into entries `di + k, …` of `dst`. -/
def decodeGo [Word32Repr α] (src : @& ByteArray) (si di cnt k : USize) (dst : Array α)
    (_hk : k ≤ cnt) (hs : 4 * (si.toNat + cnt.toNat) ≤ src.size)
    (hd : di.toNat + cnt.toNat ≤ dst.size)
    (hu : src.size < USize.size ∧ dst.size < USize.size) : Array α :=
  if hlt : k < cnt then
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    have hkn : k.toNat < cnt.toNat := hlt
    have ha : (si + k).toNat = si.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hb : (di + k).toNat = di.toNat + k.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hk1 : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by
      have := cnt.toNat_lt_size; omega)
    decodeGo src si di cnt (k + 1)
      (dst.uset (di + k)
        (Word32Repr.ofWord (readWordU src (si + k) src.size (by omega) (Nat.le_refl _) hu.1))
        (by omega))
      (by rw [USize.le_iff_toNat_le, hk1]; omega) hs
      (by simp only [Array.size_uset]; exact hd) (by simp only [Array.size_uset]; exact hu)
  else dst
termination_by cnt.toNat - k.toNat
decreasing_by
  have : k.toNat < cnt.toNat := hlt
  have : (k + 1).toNat = k.toNat + 1 := Plan.usize_add_one k (by
    have := cnt.toNat_lt_size; omega)
  omega

/-- Decode `cnt` words of `src` from `si` into `dst` from `di`; out-of-range copies do
nothing. -/
def decodeRange [Word32Repr α] (src : @& ByteArray) (si : Nat) (dst : Array α) (di cnt : Nat) :
    Array α :=
  if h : 4 * (si + cnt) ≤ src.size ∧ di + cnt ≤ dst.size ∧ src.size < USize.size ∧
      dst.size < USize.size then
    decodeGo src (USize.ofNatLT si (by omega)) (USize.ofNatLT di (by omega))
      (USize.ofNatLT cnt (by omega)) 0 dst (by simp only [USize.zero_le])
      (by simp only [USize.toNat_ofNatLT]; omega) (by simp only [USize.toNat_ofNatLT]; omega)
      ⟨h.2.2.1, h.2.2.2⟩
  else dst

/-- Row `l` of every column result, in column order. -/
def gatherLeaf [Zero α] [Word32Repr α] (cols : @& Array ByteArray) (cs l : Nat) : Array α :=
  (List.range cols.size).foldl
    (fun acc s ↦ decodeRange (cols.getD s ByteArray.empty) (l * cs) acc (s * cs) cs)
    (Array.replicate (cols.size * cs) 0)

theorem toNat_usize_le (a : Array α) : a.usize.toNat ≤ a.size := by
  simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
  exact Nat.mod_le _ _

/-- Store `v` at `i`; out-of-range stores do nothing. -/
@[inline] def setW (a : Array α) (i : USize) (v : α) : Array α :=
  if h : i < a.usize then
    a.uset i v (Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp h) (toNat_usize_le a))
  else a

open ByteWords in
/-- Store entries `q, …, M - 1` of the bit-reversed `a`, optionally scaled by `f`, as words
`off + q, …` of `out`. -/
def reverseEncodeGo [Mul α] [Word32Repr α] (a : @& Array α) (shift : UInt32) (scale : Bool)
    (f : α) (off M q : USize) (out : ByteArray) (hd : 4 * (off.toNat + M.toNat) ≤ out.size)
    (hu : out.size < USize.size) : ByteArray :=
  if hq : q < M then
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    have hqM : q.toNat < M.toNat := hq
    have ho : (off + q).toNat = off.toNat + q.toNat := by
      rw [USize.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    let j := (reverse32 q.toUInt32 >>> shift).toUSize
    if h : j.toNat < a.size then
      let v := a.uget j h
      reverseEncodeGo a shift scale f off M (q + 1)
        (writeWordU out (off + q) (Word32Repr.toWord (if scale then f * v else v)) (by omega) hu)
        (by simp only [size_writeWordU]; exact hd) (by simp only [size_writeWordU]; exact hu)
    else out
  else out
termination_by M.toNat - q.toNat
decreasing_by
  have : q.toNat < M.toNat := hq
  have : (q + 1).toNat = q.toNat + 1 := Plan.usize_add_one q (by
    have := M.toNat_lt_size; omega)
  omega

/-- A `2 ^ m`-entry array in bit-reversed order, optionally scaled by `f`, as words after
`off` padding words. -/
def reverseEncode [Mul α] [Word32Repr α] (m : Nat) (scale : Bool) (f : α) (a : @& Array α)
    (off : Nat) : ByteArray :=
  let out := ByteWords.buffer (4 * (off + 2 ^ m))
  if h : 4 * (off + 2 ^ m) < USize.size then
    have := Nat.two_pow_pos m
    reverseEncodeGo a (32 - m).toUInt32 scale f (USize.ofNatLT off (by omega))
      (USize.ofNatLT (2 ^ m) (by omega)) 0 out
      (by simp only [USize.toNat_ofNatLT, out, ByteWords.size_buffer]; omega)
      (by simp only [out, ByteWords.size_buffer]; exact h)
  else out

/-- Leaf `l`: collect its row, run the remaining passes and reverse its bit order, and store
it after `16 l` padding words. -/
@[specialize] def leafTask [Field R] [DecidableEq R] [Word32Repr R] (cols : @& Array ByteArray)
    (tw : @& Array (Array R)) (rest : List Nat) (m cs l : Nat) (scale : Bool) (f : R) :
    ByteArray :=
  reverseEncode m scale f (Parallel.runPasses false tw rest (gatherLeaf cols cs l)) (16 * l)

/-- Word `o + q` of a stored leaf is in range. -/
theorem leafIndex (M q o : USize) (hq : q < M) (s : Nat)
    (h : 4 * (o.toNat + M.toNat) ≤ s) (hs : s < USize.size) :
    4 * (o + q).toNat + 4 ≤ s := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hqM : q.toNat < M.toNat := hq
  rw [USize.toNat_add, hsize, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Store natural-order entries `16 * q + c` from the stored leaves, for `q` from `q` to
`M - 1`. Entry `16 * q + c` is entry `q` of leaf `bitrev₄ c`, stored as word `16 l + q`. -/
def assembleGo [Word32Repr α] (r : @& Array ByteArray) (M : USize) (hr : r.size = 16)
    (hb : ∀ l (h : l < 16), 4 * (16 * l + M.toNat) ≤ (r[l]'(by omega)).size ∧
      (r[l]'(by omega)).size < USize.size)
    (q : USize) (out : Array α) : Array α :=
  if hq : q < M then
    let i := 16 * q
    let out := setW out i (Word32Repr.ofWord (ByteWords.readWordU (r[0]'(by omega))
      (0 + q) _ (leafIndex M q 0 hq _ (by simpa using (hb 0 (by decide)).1)
        (hb 0 (by decide)).2) (Nat.le_refl _) (hb 0 (by decide)).2))
    let out := setW out (i + 1) (Word32Repr.ofWord (ByteWords.readWordU (r[8]'(by omega))
      (128 + q) _ (leafIndex M q 128 hq _ (by simpa using (hb 8 (by decide)).1)
        (hb 8 (by decide)).2) (Nat.le_refl _) (hb 8 (by decide)).2))
    let out := setW out (i + 2) (Word32Repr.ofWord (ByteWords.readWordU (r[4]'(by omega))
      (64 + q) _ (leafIndex M q 64 hq _ (by simpa using (hb 4 (by decide)).1)
        (hb 4 (by decide)).2) (Nat.le_refl _) (hb 4 (by decide)).2))
    let out := setW out (i + 3) (Word32Repr.ofWord (ByteWords.readWordU (r[12]'(by omega))
      (192 + q) _ (leafIndex M q 192 hq _ (by simpa using (hb 12 (by decide)).1)
        (hb 12 (by decide)).2) (Nat.le_refl _) (hb 12 (by decide)).2))
    let out := setW out (i + 4) (Word32Repr.ofWord (ByteWords.readWordU (r[2]'(by omega))
      (32 + q) _ (leafIndex M q 32 hq _ (by simpa using (hb 2 (by decide)).1)
        (hb 2 (by decide)).2) (Nat.le_refl _) (hb 2 (by decide)).2))
    let out := setW out (i + 5) (Word32Repr.ofWord (ByteWords.readWordU (r[10]'(by omega))
      (160 + q) _ (leafIndex M q 160 hq _ (by simpa using (hb 10 (by decide)).1)
        (hb 10 (by decide)).2) (Nat.le_refl _) (hb 10 (by decide)).2))
    let out := setW out (i + 6) (Word32Repr.ofWord (ByteWords.readWordU (r[6]'(by omega))
      (96 + q) _ (leafIndex M q 96 hq _ (by simpa using (hb 6 (by decide)).1)
        (hb 6 (by decide)).2) (Nat.le_refl _) (hb 6 (by decide)).2))
    let out := setW out (i + 7) (Word32Repr.ofWord (ByteWords.readWordU (r[14]'(by omega))
      (224 + q) _ (leafIndex M q 224 hq _ (by simpa using (hb 14 (by decide)).1)
        (hb 14 (by decide)).2) (Nat.le_refl _) (hb 14 (by decide)).2))
    let out := setW out (i + 8) (Word32Repr.ofWord (ByteWords.readWordU (r[1]'(by omega))
      (16 + q) _ (leafIndex M q 16 hq _ (by simpa using (hb 1 (by decide)).1)
        (hb 1 (by decide)).2) (Nat.le_refl _) (hb 1 (by decide)).2))
    let out := setW out (i + 9) (Word32Repr.ofWord (ByteWords.readWordU (r[9]'(by omega))
      (144 + q) _ (leafIndex M q 144 hq _ (by simpa using (hb 9 (by decide)).1)
        (hb 9 (by decide)).2) (Nat.le_refl _) (hb 9 (by decide)).2))
    let out := setW out (i + 10) (Word32Repr.ofWord (ByteWords.readWordU (r[5]'(by omega))
      (80 + q) _ (leafIndex M q 80 hq _ (by simpa using (hb 5 (by decide)).1)
        (hb 5 (by decide)).2) (Nat.le_refl _) (hb 5 (by decide)).2))
    let out := setW out (i + 11) (Word32Repr.ofWord (ByteWords.readWordU (r[13]'(by omega))
      (208 + q) _ (leafIndex M q 208 hq _ (by simpa using (hb 13 (by decide)).1)
        (hb 13 (by decide)).2) (Nat.le_refl _) (hb 13 (by decide)).2))
    let out := setW out (i + 12) (Word32Repr.ofWord (ByteWords.readWordU (r[3]'(by omega))
      (48 + q) _ (leafIndex M q 48 hq _ (by simpa using (hb 3 (by decide)).1)
        (hb 3 (by decide)).2) (Nat.le_refl _) (hb 3 (by decide)).2))
    let out := setW out (i + 13) (Word32Repr.ofWord (ByteWords.readWordU (r[11]'(by omega))
      (176 + q) _ (leafIndex M q 176 hq _ (by simpa using (hb 11 (by decide)).1)
        (hb 11 (by decide)).2) (Nat.le_refl _) (hb 11 (by decide)).2))
    let out := setW out (i + 14) (Word32Repr.ofWord (ByteWords.readWordU (r[7]'(by omega))
      (112 + q) _ (leafIndex M q 112 hq _ (by simpa using (hb 7 (by decide)).1)
        (hb 7 (by decide)).2) (Nat.le_refl _) (hb 7 (by decide)).2))
    let out := setW out (i + 15) (Word32Repr.ofWord (ByteWords.readWordU (r[15]'(by omega))
      (240 + q) _ (leafIndex M q 240 hq _ (by simpa using (hb 15 (by decide)).1)
        (hb 15 (by decide)).2) (Nat.le_refl _) (hb 15 (by decide)).2))
    assembleGo r M hr hb (q + 1) out
  else out
termination_by M.toNat - q.toNat
decreasing_by
  have : q.toNat < M.toNat := hq
  have : (q + 1).toNat = q.toNat + 1 := Plan.usize_add_one q (by
    have := M.toNat_lt_size; omega)
  omega

/-- Interleave sixteen stored `M`-entry leaves into natural order, writing into `out`. -/
def assemble [Word32Repr α] (r : @& Array ByteArray) (M : Nat) (out : Array α) : Array α :=
  if hM : M < USize.size then
    if hr : r.size = 16 then
      if hb : (List.range 16).all (fun l ↦ decide (4 * (16 * l + M) ≤
          (r.getD l ByteArray.empty).size ∧ (r.getD l ByteArray.empty).size < USize.size)) then
        assembleGo r (USize.ofNatLT M hM) hr (fun l h ↦ by
          have := of_decide_eq_true (List.all_eq_true.mp hb l (List.mem_range.mpr h))
          simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (show l < r.size by
            omega), Option.getD_some] at this
          simpa only [USize.toNat_ofNatLT] using this) 0 out
      else out
    else out
  else out

/-- Wait for every task without blocking a worker; results keep the task order. -/
def joinTasks (ts : Array (Task α)) : Task (Array α) :=
  ts.foldl (fun acc t ↦ acc.bind (sync := true) fun xs ↦ t.map (sync := true) fun x ↦ xs.push x)
    (.pure #[])

/-- The complete column-parallel transform: natural-order input, natural-order output,
optionally scaled by `f`; `rest` are the passes of a `2 ^ (logN - 4)`-entry leaf. -/
@[specialize] def transform [Field R] [DecidableEq R] [Word32Repr R] (tw : Array (Array R))
    (logN S : Nat) (rest : List Nat) (scale : Bool) (f : R) (x : Array R) : Array R :=
  let M := 2 ^ (logN - 4)
  let cs := M / S
  let cols := (Array.range S).map fun s ↦ Task.spawn fun _ ↦
    encode (columnTask x tw logN M cs (s * cs)) 0
  let all := joinTasks cols
  let leaves := (Array.range 16).map fun l ↦ all.bind fun cols ↦ Task.spawn fun _ ↦
    leafTask cols tw rest (logN - 4) cs l scale f
  -- allocated while the tasks run
  let out := Array.replicate (16 * M) 0
  assemble (leaves.map Task.get) M out

end CompPoly.CPolynomial.NTTFast.Columns
