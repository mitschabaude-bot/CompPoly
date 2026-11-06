/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Native
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Plan
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Kernel
public import CompPoly.Fields.Binary.AdditiveNTT.Packed.Transform
/-! # Packed bit-plane stage sweeps -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace AdditiveNTT.Bitsliced
open BF64

/-- The plane row of a sixty-four-coordinate packed block. -/
abbrev Rows (rows : Nat) := BF64.Packed.Buffer (rows * 64)

theorem row_fits (row : Nat) (hrow : row < rows)
    (hn : 8 * (rows * 64) < 4294967296) :
    (USize.ofNat (row * 64)).toNat + 64 ≤ rows * 64 := by
  rw [Native.ofNat_toNat _ (by omega)]
  omega

/-- A machine row index has a checked word address. -/
theorem machine_row (r : USize) (hr : r.toNat < rows)
    (hn : 8 * (rows * 64) < 4294967296) : (r * 64).toNat + 64 ≤ rows * 64 := by
  rw [USize.toNat_mul, Native.small 64 (by decide),
    Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]
  omega

/-- Apply a checked row operation to every row in place. -/
@[specialize] def mapRows (a : Rows rows) (hn : 8 * (rows * 64) < 4294967296)
    (f : Block → Block) : Rows rows :=
  fold (USize.ofNat rows) (fun r hr a =>
    have hr' : r.toNat < rows := by
      have := USize.lt_iff_toNat_lt.mp hr
      rwa [Native.ofNat_toNat rows (by omega)] at this
    let base := r * 64
    Native.store a hn base (machine_row r hr' hn)
      (f (Native.load a hn base (machine_row r hr' hn)))) a

/-- Interchange lane words and planes in place. -/
def transposeRows (a : Rows rows) (hn : 8 * (rows * 64) < 4294967296) : Rows rows :=
  mapRows a hn transpose

/-- Fill row-major lanes and transpose every row once during materialization. -/
@[specialize] def fromFn (rows : Nat) (hn : 8 * (rows * 64) < 4294967296)
    (f : Fin rows → Fin 64 → UInt64) : Rows rows :=
  fold (USize.ofNat rows) (fun r hr a =>
    have hr' : r.toNat < rows := by
      have := USize.lt_iff_toNat_lt.mp hr
      rwa [Native.ofNat_toNat rows (by omega)] at this
    Native.store a hn (r * 64) (machine_row r hr' hn)
      (transpose (Block.ofFn (f ⟨r.toNat, hr'⟩)))) ⟨BF64.Packed.zeros (rows * 64), rfl⟩

/-- Machine multiplication preserves bounded row offsets. -/
theorem row_mul (r : USize) (hr : r.toNat < rows)
    (hn : 8 * (rows * 64) < 4294967296) : (r * 64).toNat = r.toNat * 64 := by
  rw [USize.toNat_mul, Native.small 64 (by decide),
    Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]

/-- One row pair has its shared-scalar binary map prepared outside the inner sweep. -/
@[specialize] def stageSweep (kernel : Block → Block → Block → Scratch → (Block × Block) × Scratch)
    (p : Plan β d hd) (i : Fin d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) : Rows (2 ^ d) :=
  let span := 2 ^ i.val
  let blocks := 2 ^ (d - i.val - 1)
  have hcount : blocks * (2 * span) * 64 = 2 ^ d * 64 := by
    simpa only [Nat.mul_assoc] using Packed.stage_word_count d i 64
  have hspan : span ≤ 2 ^ d := by
    dsimp [span]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt i.isLt)
  have hb : blocks < 4294967296 := by
    have hp : 0 < span := by dsimp [span]; positivity
    nlinarith
  have hblocks : blocks ≤ 2 ^ d := by
    have hp : 0 < span := by dsimp [span]; positivity
    nlinarith
  have hs : span < 4294967296 := by omega
  let scratch : Scratch := ⟨ByteArray.zeros 2048, ByteArray.size_zeros _⟩
  (fold (USize.ofNat blocks) (fun u hu (state : Rows (2 ^ d) × Scratch) =>
    have hu' : u.toNat < blocks := by
      have := USize.lt_iff_toNat_lt.mp hu
      rwa [Native.ofNat_toNat _ hb] at this
    let m := matrix (Native.read ⟨p.words[i.val], p.size_eq i⟩ (by omega) u hu')
    let base := u * USize.ofNat (2 * span * 64)
    let stride := USize.ofNat (span * 64)
    have hbase : base.toNat = u.toNat * (2 * span) * 64 := by
      have he : base = USize.ofNat (u.toNat * (2 * span) * 64) := by
        simp only [base, Nat.mul_assoc, USize.ofNat_mul, USize.ofNat_toNat]
      rw [he, Native.ofNat_toNat _ (by nlinarith)]
    have hstride : stride.toNat = span * 64 := by
      rw [Native.ofNat_toNat _ (by omega)]
    fold (USize.ofNat span) (fun r hr (state : Rows (2 ^ d) × Scratch) =>
      have hr' : r.toNat < span := by
        have := USize.lt_iff_toNat_lt.mp hr
        rwa [Native.ofNat_toNat _ hs] at this
      let lower := base + r * 64
      let upper := lower + stride
      have hlo : (u.toNat * (2 * span) + r.toNat) * 64 + 64 ≤ 2 ^ d * 64 := by nlinarith
      have hhi : (u.toNat * (2 * span) + r.toNat) * 64 + span * 64 + 64 ≤ 2 ^ d * 64 := by nlinarith
      have hlow : lower.toNat = (u.toNat * (2 * span) + r.toNat) * 64 := by
        dsimp [lower]
        rw [Native.add_toNat _ _ (by
            rw [hbase, row_mul r (lt_of_lt_of_le hr' hspan) hn]
            nlinarith),
          hbase, row_mul r (lt_of_lt_of_le hr' hspan) hn]
        omega
      have hupp : upper.toNat = (u.toNat * (2 * span) + r.toNat) * 64 + span * 64 := by
        dsimp [upper]
        rw [Native.add_toNat _ _ (by rw [hlow, hstride]; omega), hlow, hstride]
      have hlo' : lower.toNat + 64 ≤ 2 ^ d * 64 := by rw [hlow]; exact hlo
      have hhi' : upper.toNat + 64 ≤ 2 ^ d * 64 := by rw [hupp]; exact hhi
      let u := Native.load state.1 hn lower hlo'
      let v := Native.load state.1 hn upper hhi'
      let out := kernel m u v state.2
      (Native.store (Native.store state.1 hn lower hlo' out.1.1)
        hn upper hhi' out.1.2, out.2)) state) (a, scratch)).1

/-- One forward bit-plane stage. -/
def forwardStage (p : Plan β d hd) (i : Fin d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) : Rows (2 ^ d) :=
  stageSweep forwardKernel p i a hn

/-- One inverse bit-plane stage. -/
def inverseStage (p : Plan β d hd) (i : Fin d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) : Rows (2 ^ d) :=
  stageSweep inverseKernel p i a hn

/-- Descending additive stages in the bit-plane representation. -/
def forward (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) : Rows (2 ^ d) :=
  Fin.foldl ell (fun a k => forwardStage p ⟨ell - k.val - 1, by omega⟩ a hn) a

/-- Ascending inverse additive stages in the bit-plane representation. -/
def inverse (p : Plan β d hd) (ell : Nat) (hell : ell ≤ d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) : Rows (2 ^ d) :=
  Fin.foldl ell (fun a k => inverseStage p ⟨k.val, by omega⟩ a hn) a

end AdditiveNTT.Bitsliced
