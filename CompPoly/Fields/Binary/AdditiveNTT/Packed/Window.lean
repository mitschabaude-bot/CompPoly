/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Fused

/-! # Cache-window additive transforms with addressed twiddles -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace AdditiveNTT.Packed.Window
open BF64
open AdditiveNTT.Bitsliced.Native
open Scalar

/-- Mathematical power-of-two counts for addressed transform windows. -/
def powerOfTwo (n : Nat) : Nat := 2 ^ n

/-- Native shifts compute the addressed window widths. -/
def powerOfTwoFast (n : Nat) : Nat := 1 <<< n

/-- Shift-based counts avoid generic exponentiation in dynamic window addresses. -/
@[csimp] theorem powerOfTwo_code : powerOfTwo = powerOfTwoFast := by
  funext n
  simp only [powerOfTwo, powerOfTwoFast, Nat.shiftLeft_eq, Nat.one_mul]

/-- Copy an aligned contiguous word interval into an independently owned byte buffer. -/
def slice (a : BF64.Packed.Buffer n) (start count : Nat) (h : start + count ≤ n) :
    BF64.Packed.Buffer count :=
  ⟨⟨count, a.val.bytes.extract (8 * start) (8 * (start + count)), by
    rw [ByteArray.size_extract, a.val.byteSize, a.property]
    omega⟩, rfl⟩

/-- Reading a bounded byte slice is reading the original byte address. -/
theorem byte_slice (a : ByteArray) (start count j : Nat)
    (h : start + count ≤ a.size) (hj : j < count) :
    (a.extract start (start + count))[j]! = a[start + j]! := by
  have hs : j < (a.extract start (start + count)).size := by
    rw [ByteArray.size_extract]; omega
  rw [getElem!_pos (a.extract start (start + count)) j hs, ByteArray.getElem_extract,
    getElem!_pos a (start + j) (by omega)]

/-- Reading a little-endian word commutes with a bounded byte slice. -/
theorem uint32_slice (a : ByteArray) (start count j : Nat)
    (h : start + count ≤ a.size) (hj : j + 4 ≤ count) :
    (a.extract start (start + count)).getUInt32LE! j = a.getUInt32LE! (start + j) := by
  have hs : j + 4 ≤ (a.extract start (start + count)).size := by
    rw [ByteArray.size_extract]; omega
  simp only [ByteArray.getUInt32LE!, hs, show start + j + 4 ≤ a.size by omega,
    ite_true, ByteArray.get!_eq_getElem!]
  rw [byte_slice _ _ _ _ h (by omega), byte_slice _ _ _ _ h (by omega),
    byte_slice _ _ _ _ h (by omega), byte_slice _ _ _ _ h (by omega)]
  simp only [Nat.add_assoc]

/-- A sliced packed word has its original global address. -/
@[simp] theorem read_slice (a : BF64.Packed.Buffer n) (start count : Nat)
    (h : start + count ≤ n) (j : Fin count) :
    BF64.Packed.read (slice a start count h) j =
      BF64.Packed.read a ⟨start + j.val, by have := j.isLt; omega⟩ := by
  have hb : 8 * start + 8 * count ≤ a.val.bytes.size := by
    rw [a.val.byteSize, a.property]; omega
  have he : 8 * (start + count) = 8 * start + 8 * count := by omega
  simp only [slice, BF64.Packed.read, BF64.Packed.get, ByteArray.getUInt32LE, he]
  rw [uint32_slice _ _ _ _ hb (by have := j.isLt; omega),
    uint32_slice _ _ _ _ hb (by have := j.isLt; omega)]
  simp only [Nat.mul_add, Nat.add_assoc]

/-- Concatenate equally sized byte chunks. -/
def chunks {width : Nat} : List (Bytes width) → ByteArray
  | [] => ByteArray.empty
  | x :: xs => x.val ++ chunks xs

/-- Concatenated byte chunks retain their complete combined length. -/
@[simp] theorem size_chunks (xs : List (Bytes width)) :
    (chunks xs).size = 8 * width * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [chunks, ByteArray.size_append, x.property, ih, List.length_cons]
    ring

/-- Every flat chunk can be extracted without looking at any other chunk. -/
theorem extract_chunks (xs : List (Bytes width)) (i : Nat) (hi : i < xs.length) :
    (chunks xs).extract (8 * width * i) (8 * width * (i + 1)) = (xs[i]).val := by
  induction xs generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [chunks, Nat.mul_zero, Nat.zero_add, Nat.mul_one, List.getElem_cons_zero]
      exact ByteArray.extract_append_eq_left x.property.symm
    | succ i =>
      have he : 8 * width * (i + 1) = x.val.size + 8 * width * i := by rw [x.property]; ring
      have he' : 8 * width * (i + 1 + 1) = x.val.size + 8 * width * (i + 1) := by
        rw [x.property]; ring
      simpa only [chunks, he, he', ByteArray.extract_append_size_add,
        List.getElem_cons_succ] using ih i (by simp only [List.length_cons] at hi; omega)

/-- A growing flat allocation for equally sized chunks. -/
def chunksFold (xs : List (Bytes width)) : ByteArray :=
  xs.foldl (fun bytes chunk => bytes ++ chunk.val) ByteArray.empty

/-- Growing-buffer concatenation preserves all bytes. -/
@[csimp] theorem chunks_code : @chunks = @chunksFold := by
  funext width xs
  have aux (xs : List (Bytes width)) (bytes : ByteArray) :
      xs.foldl (fun bytes chunk => bytes ++ chunk.val) bytes = bytes ++ chunks xs := by
    induction xs generalizing bytes with
    | nil => simp only [List.foldl_nil, chunks, ByteArray.append_empty]
    | cons x xs ih => rw [List.foldl_cons, ih, chunks, ByteArray.append_assoc]
  simpa only [chunksFold, ByteArray.empty_append] using (aux xs ByteArray.empty).symm

/-- Join worker results in their original address order. -/
def join (buffers : Vector (BF64.Packed.Buffer width) count) :
    BF64.Packed.Buffer (count * width) :=
  ⟨⟨count * width, chunks (buffers.toList.map unpack), by
    rw [size_chunks, List.length_map, Vector.length_toList]
    ring⟩, rfl⟩

/-- Equal byte buffers are equal packed buffers. -/
theorem bytes_ext (a b : BF64.Packed.Buffer n) (h : a.val.bytes = b.val.bytes) : a = b := by
  rcases a with ⟨⟨asize, abytes, ha⟩, ea⟩
  rcases b with ⟨⟨bsize, bbytes, hb⟩, eb⟩
  change asize = n at ea
  change bsize = n at eb
  subst asize
  subst bsize
  cases h
  rfl

/-- Extracting a joined result recovers that worker's complete buffer. -/
theorem slice_join (buffers : Vector (BF64.Packed.Buffer width) count) (i : Fin count) :
    slice (join buffers) (i.val * width) width (by have := i.isLt; nlinarith) = buffers[i.val] := by
  apply bytes_ext
  change (chunks (buffers.toList.map unpack)).extract (8 * (i.val * width))
    (8 * (i.val * width + width)) = _
  rw [show 8 * (i.val * width) = 8 * width * i.val by ring,
    show 8 * (i.val * width + width) = 8 * width * (i.val + 1) by ring]
  rw [extract_chunks _ i.val (by simp only [List.length_map, Vector.length_toList]; exact i.isLt)]
  simp only [List.getElem_map, Vector.getElem_toList, unpack]

/-- Reading a joined worker result preserves both the worker and local word coordinates. -/
@[simp] theorem read_join (buffers : Vector (BF64.Packed.Buffer width) count)
    (i : Fin count) (j : Fin width) :
    BF64.Packed.read (join buffers) (finProdFinEquiv (i, j)) =
      BF64.Packed.read buffers[i.val] j := by
  have h := congrArg (fun a => BF64.Packed.read a j) (slice_join buffers i)
  rw [read_slice] at h
  simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm] using h

/-- Scalar twiddles for a window, including its global coset offset. -/
abbrev Twiddles (d : Nat) := (i : Fin d) → Fin (2 ^ (d - i.val - 1)) → Word

/-- One window stage, partitioned into disjoint pairs. -/
def stage (p : Twiddles d) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  sweep (stageIndex d i lanes) (fun j => forwardPair (Multiplier.masked (p i j.divNat))) a

/-- Arithmetic traversal of a window stage. -/
@[specialize] def stageArithmetic (p : Twiddles d) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  Fin.foldl (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes)) (fun a j =>
    let lo := lowerIndex d i lanes j
    let hi := upperIndex d i lanes j
    let u := BF64.Packed.read a lo
    let v := BF64.Packed.read a hi
    let out := forwardPair (Multiplier.masked (p i j.divNat)) u v
    BF64.Packed.write (BF64.Packed.write a lo out.1) hi out.2) a


/-- Arithmetic and disjoint window partitions agree. -/
theorem stageArithmetic_eq (p : Twiddles d) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    stageArithmetic p i lanes a =
      stage p i lanes a := by
  unfold stageArithmetic stage sweep
  apply congrArg (fun f : BF64.Packed.Buffer (2 ^ d * lanes) →
    Fin (2 ^ (d - i.val - 1) * (2 ^ i.val * lanes)) →
    BF64.Packed.Buffer (2 ^ d * lanes) => Fin.foldl _ f a)
  funext a j
  simp only [lowerIndex_eq, upperIndex_eq, updatePair]


/-- Machine-addressed window stage. -/
def stageNative (p : Twiddles d) (i : Fin d) (lanes : Nat)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    BF64.Packed.Buffer (2 ^ d * lanes) :=
  let span := 2 ^ i.val * lanes
  let blocks := 2 ^ (d - i.val - 1)
  have hcount : blocks * (2 * span) = 2 ^ d * lanes := stage_word_count d i lanes
  have hpos : 0 < span := Nat.mul_pos (by positivity) hlanes
  have hb : blocks < 4294967296 := by nlinarith
  have hs : span < 4294967296 := by
    have hblocks : 0 < blocks := by dsimp [blocks]; positivity
    nlinarith
  let stride := USize.ofNat span
  have hstride : stride.toNat = span := ofNat_toNat _ hs
  have hdouble : (stride + stride).toNat = 2 * span := by
    rw [add_toNat _ _ (by
      rw [hstride]
      have hblocks : 0 < blocks := by dsimp [blocks]; positivity
      nlinarith), hstride]
    omega
  let stageTwiddle := p i
  pack <| foldSmall blocks hb (fun u hu a =>
    let t := (stageTwiddle ⟨u.toNat, hu⟩).val
    let base := u * (stride + stride)
    have hbase : base.toNat = u.toNat * (2 * span) := by
      rw [mul_toNat _ _ (by rw [hdouble]; nlinarith), hdouble]
    foldSmall span hs (fun j hj a =>
      let lo := base + j
      let hi := lo + stride
      have hlow : lo.toNat = u.toNat * (2 * span) + j.toNat := by
        rw [add_toNat _ _ (by rw [hbase]; nlinarith), hbase]
      have hhigh : hi.toNat = u.toNat * (2 * span) + j.toNat + span := by
        rw [add_toNat _ _ (by rw [hlow, hstride]; nlinarith), hlow, hstride]
      unpack (butterfly (pack a) hn lo hi
        (by rw [hlow]; nlinarith) (by rw [hhigh]; nlinarith) t)) a) (unpack a)


/-- Machine window stages preserve every output coordinate. -/
theorem stageNative_eq (p : Twiddles d) (i : Fin d) (lanes : Nat)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    stageNative p i lanes hlanes a hn = stage p i lanes a := by
  rw [← stageArithmetic_eq]
  unfold stageNative stageArithmetic
  rw [foldSmall_pack, pack_unpack, foldl_blocks, foldSmall_eq]
  congr 1
  funext a b
  rw [foldSmall_pack]
  simp only [pack_unpack, foldSmall_eq]
  congr 1
  funext a j
  have hs : 2 ^ i.val * lanes < 4294967296 := by
    have := stage_word_count d i lanes
    have : 0 < 2 ^ (d - i.val - 1) := by positivity
    nlinarith
  have hb : b.val < 4294967296 := by
    have := stage_word_count d i lanes
    have := b.isLt
    have : 0 < 2 ^ i.val * lanes := by positivity
    nlinarith
  have hj : j.val < 4294967296 := lt_trans j.isLt hs
  have hlo : b.val * (2 * (2 ^ i.val * lanes)) + j.val < 4294967296 := by
    have := stage_word_count d i lanes
    have := b.isLt
    have := j.isLt
    nlinarith
  have hhi : b.val * (2 * (2 ^ i.val * lanes)) + j.val + 2 ^ i.val * lanes <
      4294967296 := by
    have := stage_word_count d i lanes
    have := b.isLt
    have := j.isLt
    nlinarith
  simp only [← USize.ofNat_add, ← USize.ofNat_mul, ← two_mul, butterfly_eq,
    ofNat_toNat _ hlo, ofNat_toNat _ hhi, ofNat_toNat _ hb,
    lowerIndex, upperIndex, Fin.divNat]
  simp only [Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ i.val * lanes),
    Nat.div_eq_of_lt j.isLt, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt j.isLt]
  simp only [Nat.mul_comm, Nat.add_comm]



/-- Read one side of a complete certified scalar stage. -/
theorem read_forwardStage_pair (p : Twiddles d) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (g : Fin (2 ^ (d - i.val - 1))) (v : Fin (2 ^ i.val * lanes)) (b : Fin 2) :
    BF64.Packed.read (stage p i lanes a)
      (stageIndex d i lanes (finProdFinEquiv (g, v), b)) =
      let out := forwardPair ((fun i g => Multiplier.masked (p i g)) i g)
        (BF64.Packed.read a (stageIndex d i lanes (finProdFinEquiv (g, v), 0)))
        (BF64.Packed.read a (stageIndex d i lanes (finProdFinEquiv (g, v), 1)))
      if b = 0 then out.1 else out.2 := by
  rw [stage, read_sweep _ (stageIndex d i lanes).injective]
  have he : (finProdFinEquiv (g, v)).divNat = g :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (g, v))
  rw [he]

/-- An upper stage updates the separated slabs of each fused group. -/
theorem read_forwardStage_upper (p : Twiddles d) (i lanes : Nat) (hi : i + 1 < d)
    (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (g : Fin (2 ^ (d - (i + 1) - 1))) (v : Fin (2 ^ i * lanes)) (s b : Fin 2) :
    BF64.Packed.read (stage p ⟨i + 1, hi⟩ lanes a)
      (quadStageIndex d i lanes hi (finProdFinEquiv (g, v), finProdFinEquiv (b, s))) =
      let out := forwardPair ((fun i g => Multiplier.masked (p i g)) ⟨i + 1, hi⟩ g)
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
theorem read_forwardStage_lower (p : Twiddles d) (i lanes : Nat) (hi : i + 1 < d)
    (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (g : Fin (2 ^ (d - (i + 1) - 1))) (v : Fin (2 ^ i * lanes)) (s b : Fin 2) :
    BF64.Packed.read (stage p ⟨i, by omega⟩ lanes a)
      (quadStageIndex d i lanes hi (finProdFinEquiv (g, v), finProdFinEquiv (s, b))) =
      let out := forwardPair
        ((fun i g => Multiplier.masked (p i g)) ⟨i, by omega⟩ (quadLowerBlock d i hi g s))
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

/-- A fused pair of window stages. -/
def quad (p : Twiddles d) (i lanes : Nat) (hi : i + 1 < d)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  sweepQuad (quadStageIndex d i lanes hi) (fun j =>
    radix4 ((fun i g => Multiplier.masked (p i g)) ⟨i + 1, hi⟩ j.divNat)
      ((fun i g => Multiplier.masked (p i g)) ⟨i, by omega⟩ (quadLowerBlock d i hi j.divNat 0))
      ((fun i g => Multiplier.masked (p i g)) ⟨i, by omega⟩ (quadLowerBlock d i hi j.divNat 1))) a


/-- A fused radix-four sweep is exactly two complete certified stages. -/
theorem quad_eq (p : Twiddles d) (i lanes : Nat) (hi : i + 1 < d)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    quad p i lanes hi a =
      stage p ⟨i, by omega⟩ lanes (stage p ⟨i + 1, hi⟩ lanes a) := by
  apply BF64.Packed.read_ext
  intro j
  obtain ⟨⟨t, c⟩, rfl⟩ := (quadStageIndex d i lanes hi).surjective j
  obtain ⟨⟨g, v⟩, rfl⟩ := finProdFinEquiv.surjective t
  obtain ⟨⟨s, b⟩, rfl⟩ := (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).surjective c
  rw [quad, read_sweepQuad _ (quadStageIndex d i lanes hi).injective]
  have hdiv : (finProdFinEquiv (g, v)).divNat = g :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (g, v))
  simp only [hdiv]
  rw [read_forwardStage_lower, read_forwardStage_upper, read_forwardStage_upper]
  fin_cases s <;> fin_cases b <;> simp [radix4, Quad.get, finProdFinEquiv]

/-- Machine radix-four execution inside a cache window. -/
def quadNative (p : Twiddles d) (i lanes : Nat) (hi : i + 1 < d)
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
  let upperTwiddle := p ⟨i + 1, hi⟩
  let lowerTwiddle := p ⟨i, by omega⟩
  pack <| foldSmall blocks hb (fun u hu a =>
    let g : Fin blocks := ⟨u.toNat, hu⟩
    let t0 := upperTwiddle g
    let t1 := lowerTwiddle (quadLowerBlock d i hi g 0)
    let t2 := lowerTwiddle (quadLowerBlock d i hi g 1)
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


attribute [local irreducible] radix4 updateQuad

/-- The machine kernel agrees with the disjoint window sweep. -/
theorem quadNative_eq (p : Twiddles d) (i lanes : Nat) (hi : i + 1 < d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    quadNative p i lanes hi hlanes a hn = quad p i lanes hi a := by
  unfold quadNative quad sweepQuad
  rw [foldSmall_pack, pack_unpack, foldl_blocks]
  rw [foldSmall_eq]
  congr 1
  funext a g
  rw [foldSmall_pack]
  simp only [pack_unpack, foldSmall_eq]
  congr 1
  funext a v
  change _ = updateQuad (quadStageIndex d i lanes hi) (fun j =>
    radix4 ((fun i g => Multiplier.masked (p i g)) ⟨i + 1, hi⟩ j.divNat)
      ((fun i g => Multiplier.masked (p i g)) ⟨i, by omega⟩ (quadLowerBlock d i hi j.divNat 0))
      ((fun i g => Multiplier.masked (p i g)) ⟨i, by omega⟩ (quadLowerBlock d i hi j.divNat 1))) a
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
    ofNat_toNat _ hgn, updateQuad, hdiv]
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


/-- Descending stages within one addressed cache window. -/
def forwardSpec (p : Twiddles d) : (ell : Nat) → ell ≤ d → (lanes : Nat) →
    BF64.Packed.Buffer (2 ^ d * lanes) → BF64.Packed.Buffer (2 ^ d * lanes)
  | 0, _, _, a => a
  | k + 1, h, lanes, a => forwardSpec p k (by omega) lanes (stage p ⟨k, by omega⟩ lanes a)

/-- Fused machine execution of one complete window. -/
def forward (p : Twiddles d) (ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  match ell with
  | 0 => a
  | 1 => stageNative p ⟨0, by omega⟩ lanes hlanes a hn
  | k + 2 => forward p k (by omega) lanes hlanes
      (quadNative p k lanes (by omega) hlanes a hn) hn

/-- Window fusion preserves the entire descending transform. -/
theorem forward_eq (p : Twiddles d) (ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    forward p ell hell lanes hlanes a hn = forwardSpec p ell hell lanes a := by
  induction ell using Nat.twoStepInduction generalizing a with
  | zero => rfl
  | one => simp only [forward, stageNative_eq, forwardSpec]
  | more k ih _ =>
    rw [forward, ih (by omega), quadNative_eq, quad_eq, forwardSpec, forwardSpec]

/-- The words in equal power-of-two windows partition the complete domain. -/
theorem window_count (d ell lanes : Nat) (hell : ell ≤ d) :
    2 ^ (d - ell) * (2 ^ ell * lanes) = 2 ^ d * lanes := by
  rw [← Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hell]

/-- Translate a local word address into its contiguous global window. -/
def address (d ell lanes : Nat) (hell : ell ≤ d) (b : Fin (2 ^ (d - ell)))
    (j : Fin (2 ^ ell * lanes)) : Fin (2 ^ d * lanes) :=
  ⟨b.val * (2 ^ ell * lanes) + j.val, by
    have := b.isLt; have := j.isLt
    have := window_count d ell lanes hell
    nlinarith⟩

/-- Translate a stage-local block into the original plan's coset coordinate. -/
def block (d ell : Nat) (hell : ell ≤ d) (b : Fin (2 ^ (d - ell)))
    (i : Fin ell) (g : Fin (2 ^ (ell - i.val - 1))) : Fin (2 ^ (d - i.val - 1)) :=
  ⟨b.val * powerOfTwo (ell - i.val - 1) + g.val, by
    change b.val * 2 ^ (ell - i.val - 1) + g.val < 2 ^ (d - i.val - 1)
    have hc : 2 ^ (d - ell) * 2 ^ (ell - i.val - 1) = 2 ^ (d - i.val - 1) := by
      rw [← pow_add]; congr 1; have := i.isLt; omega
    have := b.isLt; have := g.isLt; nlinarith⟩

/-- Retain the global twiddle offset while addressing a smaller contiguous transform. -/
def twiddlesAt (p : Twiddles d) (ell : Nat) (hell : ell ≤ d)
    (b : Fin (2 ^ (d - ell))) : Twiddles ell :=
  fun i =>
    let stageTwiddle := p ⟨i.val, by have := i.isLt; omega⟩
    let offset := b.val * powerOfTwo (ell - i.val - 1)
    fun g => stageTwiddle ⟨offset + g.val, (block d ell hell b i g).isLt⟩

/-- Copy a contiguous window into worker-local storage. -/
def extract (a : BF64.Packed.Buffer (2 ^ d * lanes)) (ell : Nat) (hell : ell ≤ d)
    (b : Fin (2 ^ (d - ell))) : BF64.Packed.Buffer (2 ^ ell * lanes) :=
  slice a (b.val * (2 ^ ell * lanes)) (2 ^ ell * lanes) (by
    have hc := window_count d ell lanes hell
    have hb := Nat.mul_le_mul_right (2 ^ ell * lanes) (Nat.succ_le_of_lt b.isLt)
    rw [Nat.succ_mul, hc] at hb
    exact hb)

/-- A cache-window load has its original transform address. -/
@[simp] theorem read_extract (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (ell : Nat) (hell : ell ≤ d) (b : Fin (2 ^ (d - ell))) (j : Fin (2 ^ ell * lanes)) :
    BF64.Packed.read (extract a ell hell b) j =
      BF64.Packed.read a (address d ell lanes hell b j) := by
  exact read_slice ..

/-- Stage coordinates commute with a contiguous window's global offset. -/
theorem address_stage (d ell lanes : Nat) (hell : ell ≤ d)
    (b : Fin (2 ^ (d - ell))) (i : Fin ell)
    (g : Fin (2 ^ (ell - i.val - 1))) (v : Fin (2 ^ i.val * lanes)) (s : Fin 2) :
    address d ell lanes hell b (stageIndex ell i lanes (finProdFinEquiv (g, v), s)) =
      stageIndex d ⟨i.val, by have := i.isLt; omega⟩ lanes
        (finProdFinEquiv (block d ell hell b i g, v), s) := by
  apply Fin.ext
  rw [stageIndex_block_val]
  change b.val * (2 ^ ell * lanes) +
    (stageIndex ell i lanes (finProdFinEquiv (g, v), s)).val = _
  rw [stageIndex_block_val]
  change _ = v.val + (2 ^ i.val * lanes) *
    (s.val + 2 * (b.val * 2 ^ (ell - i.val - 1) + g.val))
  have hc := stage_word_count ell i lanes
  calc
    _ = b.val * (2 ^ (ell - i.val - 1) * (2 * (2 ^ i.val * lanes))) +
        (v.val + (2 ^ i.val * lanes) * (s.val + 2 * g.val)) := by rw [hc]
    _ = _ := by ring

/-- A near stage reads and writes only its own contiguous window. -/
theorem extract_stage (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (b : Fin (2 ^ (d - ell))) (i : Fin ell) (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    extract (stage p ⟨i.val, by have := i.isLt; omega⟩ lanes a) ell hell b =
      stage (twiddlesAt p ell hell b) i lanes (extract a ell hell b) := by
  apply BF64.Packed.read_ext
  intro j
  obtain ⟨⟨t, s⟩, rfl⟩ := (stageIndex ell i lanes).surjective j
  obtain ⟨⟨g, v⟩, rfl⟩ := finProdFinEquiv.surjective t
  rw [read_extract, address_stage, read_forwardStage_pair, read_forwardStage_pair]
  simp only [read_extract, address_stage, twiddlesAt, block, powerOfTwo]

/-- All near stages can finish inside their cache window before any other window is read. -/
theorem extract_forward (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (b : Fin (2 ^ (d - ell))) (k : Nat) (hk : k ≤ ell)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    extract (forwardSpec p k (by omega) lanes a) ell hell b =
      forwardSpec (twiddlesAt p ell hell b) k hk lanes (extract a ell hell b) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [forwardSpec, forwardSpec, ih (by omega)]
    rw [extract_stage p ell lanes hell b ⟨k, by omega⟩ a]

/-- A full-domain window uses the certified packed plan's exact scalar multipliers. -/
theorem stage_toPacked (p : Bitsliced.Plan β d hd) (i : Fin d) (lanes : Nat)
    (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    stage (fun i g => p.get i g) i lanes a = Packed.forwardStage p.toPacked i lanes a := by
  rw [stage, forwardStage_eq_sweep]
  simp only [Scalar.get_toPacked]

/-- Addressed descending stages agree with every certified transform prefix. -/
theorem forwardSpec_toPacked (p : Bitsliced.Plan β d hd) (ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    forwardSpec (fun i g => p.get i g) ell hell lanes a =
      Packed.forward p.toPacked ell hell lanes a := by
  induction ell generalizing a with
  | zero => simp only [forwardSpec, Packed.forward, Fin.foldl_zero]
  | succ k ih =>
    rw [forwardSpec, ih, stage_toPacked]
    unfold Packed.forward
    rw [Fin.foldl_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel]
    congr 1
    funext a j
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

/-- Group consecutive power-of-two jobs into one worker-owned task. -/
def taskMap {α : Type} (count chunk : Nat) (hc : chunk ≤ count)
    (f : Fin (2 ^ count) → α) : Vector α (2 ^ count) :=
  have size : 2 ^ (count - chunk) * 2 ^ chunk = 2 ^ count := by
    rw [← pow_add, Nat.sub_add_cancel hc]
  let jobs := Vector.ofFn fun g : Fin (2 ^ (count - chunk)) => Task.spawn fun _ =>
    Vector.ofFn fun i : Fin (2 ^ chunk) => f (Fin.cast size (finProdFinEquiv (g, i)))
  Vector.ofFn fun i =>
    let coordinate := finProdFinEquiv.symm (Fin.cast size.symm i)
    (jobs[coordinate.1.val]).get[coordinate.2.val]

/-- Batching changes only where each job runs. -/
theorem taskMap_get {α : Type} (count chunk : Nat) (hc : chunk ≤ count)
    (f : Fin (2 ^ count) → α) (i : Fin (2 ^ count)) :
    (taskMap count chunk hc f)[i.val] = f i := by
  have size : 2 ^ (count - chunk) * 2 ^ chunk = 2 ^ count := by
    rw [← pow_add, Nat.sub_add_cancel hc]
  simp only [taskMap, Task.spawn, Vector.getElem_ofFn]
  change f (Fin.cast size (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast size.symm i)))) = f i
  rw [Equiv.apply_symm_apply]
  rfl

/-- Independent sub-blocks share a task until it reaches the cache-sized row handover. -/
def taskChunk (d near lanes workers : Nat) : Nat :=
  let parallel := if 12 ≤ d then
    min (Nat.log2 (max workers 1 - 1) + if workers ≤ 1 then 0 else 1) (d - 8) else 0
  let task := max near (min (Nat.log2 (max (131072 / lanes) 1)) (d - parallel))
  min (d - near) (task - near)

/-- Finish independent contiguous windows and invoke the row sink before returning each buffer. -/
def deep {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - ell)) → BF64.Packed.Buffer (2 ^ ell * lanes) → α) :
    Vector (BF64.Packed.Buffer (2 ^ ell * lanes) × α) (2 ^ (d - ell)) :=
  taskMap (d - ell) (taskChunk d ell lanes workers) (Nat.min_le_left ..) fun b =>
    let out := forward (twiddlesAt p ell hell b) ell (by omega) lanes hlanes
      (extract a ell hell b) (by
        have hc := window_count d ell lanes hell
        have hp : 0 < 2 ^ (d - ell) := by positivity
        nlinarith)
    (out, sink b out)

/-- Every deep result is the corresponding window of the complete certified transform. -/
theorem deep_get {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - ell)) → BF64.Packed.Buffer (2 ^ ell * lanes) → α)
    (b : Fin (2 ^ (d - ell))) :
    (deep workers p ell lanes hell hlanes a hn sink)[b.val] =
      let out := extract (forwardSpec p ell hell lanes a) ell hell b
      (out, sink b out) := by
  rw [deep, taskMap_get]
  change (forward _ ell _ lanes _ _ _, sink b (forward _ ell _ lanes _ _ _)) = _
  rw [forward_eq, ← extract_forward p ell lanes hell b ell (by omega)]

/-- Descending far stages stop at the near-window boundary. -/
def farSpec (p : Twiddles d) (near : Nat) : (ell : Nat) → ell ≤ d → (lanes : Nat) →
    BF64.Packed.Buffer (2 ^ d * lanes) → BF64.Packed.Buffer (2 ^ d * lanes)
  | 0, _, _, a => a
  | k + 1, h, lanes, a =>
    if near ≤ k then farSpec p near k (by omega) lanes (stage p ⟨k, by omega⟩ lanes a) else a

/-- Splitting at the cache boundary preserves the complete descending stage order. -/
theorem farSpec_split (p : Twiddles d) (ell near lanes : Nat) (hell : ell ≤ d)
    (hnear : near ≤ ell) (a : BF64.Packed.Buffer (2 ^ d * lanes)) :
    forwardSpec p ell hell lanes a =
      forwardSpec p near (by omega) lanes (farSpec p near ell hell lanes a) := by
  induction ell generalizing a with
  | zero =>
    have he : near = 0 := by omega
    subst near
    rfl
  | succ k ih =>
    by_cases h : near ≤ k
    · rw [forwardSpec, farSpec, ite_eq_left h, ih (by omega) h]
    · have he : near = k + 1 := by omega
      subst near
      rw [farSpec, ite_eq_right (by omega)]

/-- Fused far stages, preserving the global twiddle coordinates. -/
def far (p : Twiddles d) (near : Nat) (ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) : BF64.Packed.Buffer (2 ^ d * lanes) :=
  match ell with
  | 0 => a
  | 1 => if near = 0 then stageNative p ⟨0, by omega⟩ lanes hlanes a hn else a
  | k + 2 =>
    if near ≤ k then
      far p near k (by omega) lanes hlanes (quadNative p k lanes (by omega) hlanes a hn) hn
    else if near = k + 1 then stageNative p ⟨k + 1, by omega⟩ lanes hlanes a hn else a

/-- Fused far passes stop at exactly the specified near boundary. -/
theorem far_eq (p : Twiddles d) (near ell : Nat) (hell : ell ≤ d)
    (lanes : Nat) (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296) :
    far p near ell hell lanes hlanes a hn = farSpec p near ell hell lanes a := by
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
    · rw [ite_eq_left h, ih (by omega), quadNative_eq, quad_eq, farSpec, ite_eq_left (by omega),
        farSpec, ite_eq_left h]
    · rw [ite_eq_right h, farSpec]
      by_cases he : near = k + 1
      · rw [ite_eq_left he, ite_eq_left (by omega), farSpec, ite_eq_right h, stageNative_eq]
      · rw [ite_eq_right he, ite_eq_right (by omega)]

/-- Cache budget and worker count select a Rust-style deep split. -/
def nearDepth (workers d ell lanes : Nat) : Nat :=
  let words := if 2 ^ ell * lanes ≤ 262144 then 262144 else 131072
  let fit := Nat.log2 (max (words / lanes) 1)
  let parallel := if 12 ≤ d then
    min (Nat.log2 (max workers 1 - 1) + if workers ≤ 1 then 0 else 1) (d - 8) else 0
  min ell (min fit (d - parallel))

/-- The deep split never runs stages outside the requested transform prefix. -/
theorem nearDepth_le (workers d ell lanes : Nat) :
    nearDepth workers d ell lanes ≤ ell := Nat.min_le_left ..

/-- Run far sweeps, then finish and sink independent cache windows in parallel. -/
def run {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - nearDepth workers d ell lanes)) →
      BF64.Packed.Buffer (2 ^ nearDepth workers d ell lanes * lanes) → α) :
    Vector (BF64.Packed.Buffer (2 ^ nearDepth workers d ell lanes * lanes) × α)
      (2 ^ (d - nearDepth workers d ell lanes)) :=
  let near := nearDepth workers d ell lanes
  deep workers p near lanes (le_trans (nearDepth_le ..) hell) hlanes
    (far p near ell hell lanes hlanes a hn) hn sink

/-- Each completed window and its sink observe exactly the certified full transform. -/
theorem run_get {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - nearDepth workers d ell lanes)) →
      BF64.Packed.Buffer (2 ^ nearDepth workers d ell lanes * lanes) → α)
    (b : Fin (2 ^ (d - nearDepth workers d ell lanes))) :
    (run workers p ell lanes hell hlanes a hn sink)[b.val] =
      let out := extract (forwardSpec p ell hell lanes a) (nearDepth workers d ell lanes)
        (le_trans (nearDepth_le ..) hell) b
      (out, sink b out) := by
  rw [run, deep_get, far_eq,
    ← farSpec_split p ell (nearDepth workers d ell lanes) lanes hell
    (nearDepth_le ..)]

/-- Join complete contiguous windows into a consumer-owned full-domain buffer. -/
def joinDomain (d ell lanes : Nat) (hell : ell ≤ d)
    (buffers : Vector (BF64.Packed.Buffer (2 ^ ell * lanes)) (2 ^ (d - ell))) :
    BF64.Packed.Buffer (2 ^ d * lanes) :=
  let out := join buffers
  ⟨out.val, out.property.trans (window_count d ell lanes hell)⟩

/-- Joining windows preserves the global address of each local word. -/
theorem read_joinDomain (d ell lanes : Nat) (hell : ell ≤ d)
    (buffers : Vector (BF64.Packed.Buffer (2 ^ ell * lanes)) (2 ^ (d - ell)))
    (b : Fin (2 ^ (d - ell))) (j : Fin (2 ^ ell * lanes)) :
    BF64.Packed.read (joinDomain d ell lanes hell buffers) (address d ell lanes hell b j) =
      BF64.Packed.read buffers[b.val] j := by
  have h := read_join buffers b j
  simpa only [joinDomain, address, BF64.Packed.read, finProdFinEquiv, Equiv.coe_fn_mk,
    Nat.mul_comm, Nat.add_comm] using h

/-- Complete windows cover every word of the transform domain. -/
theorem address_surjective (d ell lanes : Nat) (hell : ell ≤ d)
    (j : Fin (2 ^ d * lanes)) :
    ∃ (b : Fin (2 ^ (d - ell))) (v : Fin (2 ^ ell * lanes)), address d ell lanes hell b v = j := by
  let coordinate :=  Fin.cast (window_count d ell lanes hell).symm j
  obtain ⟨⟨b, v⟩, he⟩ := finProdFinEquiv.surjective coordinate
  refine ⟨b, v, ?_⟩
  have h := congrArg Fin.val he
  apply Fin.ext
  simpa only [address, finProdFinEquiv, Equiv.coe_fn_mk, coordinate, Fin.val_cast,
    Nat.mul_comm, Nat.add_comm] using h

/-- Return a consumer-owned codeword together with the cache-resident row-sink results. -/
def runJoined {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - nearDepth workers d ell lanes)) →
      BF64.Packed.Buffer (2 ^ nearDepth workers d ell lanes * lanes) → α) :
    BF64.Packed.Buffer (2 ^ d * lanes) × Vector α (2 ^ (d - nearDepth workers d ell lanes)) :=
  let result := run workers p ell lanes hell hlanes a hn sink
  (joinDomain d (nearDepth workers d ell lanes) lanes (le_trans (nearDepth_le ..) hell)
    (result.map Prod.fst), result.map Prod.snd)

/-- The joined codeword and all row-sink outputs agree with the certified full transform. -/
theorem runJoined_eq {α : Type} (workers : Nat) (p : Twiddles d) (ell lanes : Nat) (hell : ell ≤ d)
    (hlanes : 0 < lanes) (a : BF64.Packed.Buffer (2 ^ d * lanes))
    (hn : 8 * (2 ^ d * lanes) < 4294967296)
    (sink : Fin (2 ^ (d - nearDepth workers d ell lanes)) →
      BF64.Packed.Buffer (2 ^ nearDepth workers d ell lanes * lanes) → α) :
    runJoined workers p ell lanes hell hlanes a hn sink =
      let out := forwardSpec p ell hell lanes a
      (out, Vector.ofFn fun b => sink b (extract out (nearDepth workers d ell lanes)
        (le_trans (nearDepth_le ..) hell) b)) := by
  apply Prod.ext
  · apply BF64.Packed.read_ext
    intro j
    obtain ⟨b, v, rfl⟩ := address_surjective d (nearDepth workers d ell lanes) lanes
      (le_trans (nearDepth_le ..) hell) j
    rw [runJoined, read_joinDomain, Vector.getElem_map, run_get, read_extract]
  · apply Vector.ext
    intro i hi
    simp only [runJoined, Vector.getElem_map, Vector.getElem_ofFn]
    exact congrArg Prod.snd (run_get workers p ell lanes hell hlanes a hn sink ⟨i, hi⟩)

end AdditiveNTT.Packed.Window
