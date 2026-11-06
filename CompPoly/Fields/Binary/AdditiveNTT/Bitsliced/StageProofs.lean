/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Stage
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.RowSweep
public import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Partition
/-! # Bit-plane stage refinement through the packed row partition -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AdditiveNTT.Bitsliced

/-- Enumerating pairs is the nested block and offset traversal. -/
theorem fold_pairList (d : Nat) (i : Fin d) (f : α → PairIndex d i → α) (a : α) :
    (pairList d i).foldl f a =
      Fin.foldl (2 ^ (d - i.val - 1)) (fun a u =>
        Fin.foldl (2 ^ i.val) (fun a r => f a (u, r)) a) a := by
  simp only [pairList, Fin.foldl_eq_finRange_foldl, List.product,
    List.foldl_flatMap, List.foldl_map]

/-- The disjoint-row model of a complete bit-plane stage. -/
def rowStage (p : Plan β d hd) (i : Fin d)
    (op : UInt64 → Block → Block → Block × Block) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) : Rows (2 ^ d) :=
  (pairList d i).foldl (updateRows (rowPartition d i) hn (fun j =>
    op (BF64.Packed.read ⟨p.words[i.val], p.size_eq i⟩ j.1).val)) a

/-- A complete native stage refines the disjoint-row model. -/
theorem stageSweep_eq_rowStage
    (kernel : Block → Block → Block → Scratch → (Block × Block) × Scratch)
    (op : UInt64 → Block → Block → Block × Block)
    (hk : ∀ t u v s, (kernel (matrix t) u v s).1 = op t u v)
    (p : Plan β d hd) (i : Fin d) (a : Rows (2 ^ d))
    (hn : 8 * (2 ^ d * 64) < 4294967296) :
    stageSweep kernel p i a hn = rowStage p i op a hn := by
  let span := 2 ^ i.val
  let blocks := 2 ^ (d - i.val - 1)
  have hcount : blocks * (2 * span) * 64 = 2 ^ d * 64 := by
    simpa only [Nat.mul_assoc] using Packed.stage_word_count d i 64
  have hp : 0 < span := by dsimp [span]; positivity
  have hb : blocks < 4294967296 := by nlinarith
  have hs : span < 4294967296 := by
    have : span ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt i.isLt)
    omega
  unfold stageSweep rowStage
  dsimp only
  rw [fold_pairList]
  simp only [fold_eq]
  simp only [Native.ofNat_toNat (2 ^ (d - i.val - 1)) hb,
    Native.ofNat_toNat (2 ^ i.val) hs, Fin.val_cast]
  simp only [Native.read_eq, ← USize.ofNat_mul, ← Nat.mul_assoc]
  apply finFold_projection Prod.fst
  intro state u
  apply finFold_projection Prod.fst
  intro state r
  dsimp only
  set lo := USize.ofNat (u.val * (2 * 2 ^ i.val) * 64) + USize.ofNat r.val * 64
  set hi := lo + USize.ofNat (2 ^ i.val * 64)
  have hu := u.isLt
  have hr := r.isLt
  have hlow : u.val * (2 * 2 ^ i.val) * 64 + r.val * 64 + 64 ≤ 2 ^ d * 64 := by
    dsimp [blocks, span] at hcount hp
    nlinarith
  have hhigh : u.val * (2 * 2 ^ i.val) * 64 + r.val * 64 + 2 ^ i.val * 64 + 64 ≤ 2 ^ d * 64 := by
    dsimp [blocks, span] at hcount hp
    nlinarith
  have hbase : (USize.ofNat (u.val * (2 * 2 ^ i.val) * 64)).toNat =
      u.val * (2 * 2 ^ i.val) * 64 := Native.ofNat_toNat _ (by omega)
  have hmul : (USize.ofNat r.val * 64).toNat = r.val * 64 := by
    rw [USize.toNat_mul, Native.small 64 (by decide),
      Native.ofNat_toNat r.val (by dsimp [span] at hs; omega),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]
  have hlo : lo.toNat = (rowPartition d i ((u, r), 0)).val * 64 := by
    dsimp [lo]
    rw [Native.add_toNat _ _ (by rw [hbase, hmul]; omega), hbase, hmul,
      rowPartition_val]
    simp only [show (0 : Fin 2).val = 0 from rfl]
    ring
  have hhi : hi.toNat = (rowPartition d i ((u, r), 1)).val * 64 := by
    have hstride : (USize.ofNat (2 ^ i.val * 64)).toNat = 2 ^ i.val * 64 :=
      Native.ofNat_toNat _ (by omega)
    dsimp [hi]
    rw [Native.add_toNat _ _ (by
        rw [hlo, hstride, rowPartition_val]
        simp only [show (0 : Fin 2).val = 0 from rfl,
          Nat.mul_zero, Nat.add_zero]
        omega),
      hlo, hstride, rowPartition_val, rowPartition_val]
    simp only [show (0 : Fin 2).val = 0 from rfl, show (1 : Fin 2).val = 1 from rfl]
    ring
  dsimp only [lo, hi] at hlo hhi
  simp only [Nat.mul_assoc] at hlo hhi ⊢
  simp only [Native.ofNat_toNat u.val (by dsimp [blocks] at hb; omega)]
  simp only [load_at (hn := hn) (r := rowPartition d i ((u, r), 0)) (he := hlo),
    load_at (hn := hn) (r := rowPartition d i ((u, r), 1)) (he := hhi),
    store_at (hn := hn) (r := rowPartition d i ((u, r), 0)) (he := hlo),
    store_at (hn := hn) (r := rowPartition d i ((u, r), 1)) (he := hhi), hk, updateRows]


end AdditiveNTT.Bitsliced
