/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Packed.BasisConversion

/-! # Packed encoder, inverse, lane layout and basis-conversion regressions -/

public section

namespace CompPolyTests.Fields.Binary.AdditiveNTT.Packed

open BF64 _root_.AdditiveNTT _root_.AdditiveNTT.Packed

private def word (i : Nat) : Word := ⟨UInt64.ofNat (17 + 37 * i)⟩

private def roundtrip (ell rate lanes : Nat) (hd : ell + rate < 64) : Bool :=
  let p := Plan.create flatBasis (ell + rate) hd
  let a := tabulate (2 ^ ell * lanes) fun j => word j.val
  let code := encodeRows (ell := ell) (rate := rate) p lanes a
  let recovered := decodeRows (ell := ell) (rate := rate) p lanes code
  recovered.val.bytes == a.val.bytes


private def genericAgreement : Bool := Id.run do
  let p := Plan.create flatBasis 4 (by decide)
  let a := tabulate (2 ^ 3 * 5) fun j => word j.val
  let out := encodeRows (ell := 3) (rate := 1) p 5 a
  for lane in List.finRange 5 do
    let expected := computableAdditiveNTT (𝔽q := ZMod 2) flatBasis (by decide)
      (ℓ := 3) (R_rate := 1) (laneView a lane)
    for row in List.finRange (2 ^ 4) do
      if laneView out lane row != expected row then return false
  return true


private def initialLayout : Bool := Id.run do
  let p := Plan.create flatBasis 4 (by decide)
  let a := tabulate (5 * 2 ^ 3) fun j => word j.val
  let out := encodeInitial (ell := 3) (rate := 1) p 5 8 (by decide) a
  for lane in List.finRange 8 do
    let source := fun row : Fin (2 ^ 3) => if h : lane.val < 3 then (⟨0⟩ : Word)
      else BF64.Packed.read a ⟨(7 - lane.val) * 8 + row.val, by have := lane.isLt; omega⟩
    let expected := computableAdditiveNTT (𝔽q := ZMod 2) flatBasis (by decide)
      (ℓ := 3) (R_rate := 1) source
    for row in List.finRange (2 ^ 4) do
      if laneView out lane row != expected row then return false
  return true


local instance : Algebra (ZMod 2) Ext3 := ZMod.algebra Ext3 2

private def extensionAgreement : Bool := Id.run do
  let p := Plan.create flatBasis 3 (by decide)
  let a := tabulate (2 ^ 2 * (3 * 2)) fun j => word j.val
  let out := encodeRows (ell := 2) (rate := 1) p 6 a
  for lane in List.finRange 2 do
    let expected := computableAdditiveNTT (𝔽q := ZMod 2) extensionBasis (by decide)
      (ℓ := 2) (R_rate := 1) (extensionLaneView a lane)
    for row in List.finRange (2 ^ 3) do
      if WordExt3.ofField (extensionLaneView out lane row) != WordExt3.ofField (expected row) then
        return false
  return true


private def inverseFirst : Bool :=
  let p := Plan.create flatBasis 3 (by decide)
  let a := tabulate (2 ^ 3 * 2) fun j => word j.val
  let inverseFirst := inverse p 3 (by decide) 2 a
  (forward p 3 (by decide) 2 inverseFirst).val.bytes == a.val.bytes

private def squareConversion : Bool :=
  let polys : Fin 1 → CompPoly.CPolynomial Word := fun _ => CompPoly.CPolynomial.X ^ 2
  let a := monomialCoefficients 2 (by decide) 1 polys
  (List.finRange 4).map (laneView a 0) == [0, 1, ⟨6⟩, 0]

private def convertedRoundtrip : Bool :=
  let p := Plan.create flatBasis 4 (by decide)
  let polys : Fin 2 → CompPoly.CPolynomial Word := fun i =>
    if i.val = 0 then CompPoly.CPolynomial.X ^ 2 else CompPoly.CPolynomial.X ^ 3
  let a := monomialCoefficients 2 (by decide) 2 polys
  (decodeRows (ell := 2) (rate := 2) p 2
    (encodeRows (ell := 2) (rate := 2) p 2 a)).val.bytes == a.val.bytes

/-- Run linked checks using the approved native packed-buffer accessors. -/
def runChecks : IO Unit := do
  let checks : List (String × Bool) := [
    ("zero domain", roundtrip 0 0 1 (by decide)),
    ("zero stages", roundtrip 0 3 5 (by decide)),
    ("rate zero", roundtrip 3 0 2 (by decide)),
    ("row roundtrip", roundtrip 3 2 5 (by decide)),
    ("empty lanes", roundtrip 3 1 0 (by decide)),
    ("generic K", genericAgreement), ("initial layout", initialLayout),
    ("generic E", extensionAgreement), ("inverse first", inverseFirst),
    ("square conversion", squareConversion), ("converted roundtrip", convertedRoundtrip)]
  for (label, passed) in checks do
    unless passed do throw <| IO.userError s!"packed additive NTT failed: {label}"
  IO.println s!"packed additive NTT: {checks.length} checks passed"

end CompPolyTests.Fields.Binary.AdditiveNTT.Packed
