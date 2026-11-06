/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.GuruswamiSudan

/-! # Compiled production-size scalar GS decoding and phase profiling -/

public section

open CompPoly CompPoly.GuruswamiSudan

private def report (s : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn s
  out.flush

private def timed {α : Type} (name : String) (action : Unit → IO α) : IO α := do
  report s!"start {name}"
  let start ← IO.monoNanosNow
  let result ← action ()
  let stop ← IO.monoNanosNow
  report s!"done {name} ms={(stop - start) / 1000000}"
  return result

private def profile {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (roots : GSRootContext F) (params : GSExecParams) (w : GSReceivedWord F) :
    IO (Array (CPolynomial F)) := do
  let distinct ← timed "distinct" fun _ ↦ pure (distinctXCoordinatesBool w.points)
  unless distinct do throw <| IO.userError "duplicate abscissa"
  let V := CPolynomial.VanishingPolynomialContext.subproduct CPolynomial.MulContext.naive
  let E := CPolynomial.BatchEvalContext.subproduct F CPolynomial.MulContext.naive
    CPolynomial.ModContext.remainderOnly
  let G ← timed "vanishing" fun _ ↦ pure (V.vanishingPolynomial (w.points.map Prod.fst))
  report s!"vanishing coefficients={G.val.size}"
  let R ← timed "coefficient-interpolation" fun _ ↦
    pure (CPolynomial.interpolateCoefficientFormWithVanishing E G w.points)
  report s!"interpolant coefficients={R.val.size}"
  let basis ← timed "module-basis" fun _ ↦
    pure (leeOSullivanBasisRowsWithRG R G params.interp)
  let shift := leeOSullivanShifts params.interp
  report s!"module width={basis.size}"
  let reduced ← timed "row-reduction" fun _ ↦
    pure ((PolynomialMatrix.muldersStorjohannFastReducerContext F).reduce basis shift)
  let some row := LeeOSullivan.leastShiftedDegreeRow? reduced shift |
    throw <| IO.userError "no interpolation row"
  let some Q ← timed "normalization" fun _ ↦
      pure (LeeOSullivan.normalizeLeeCandidate? params.interp (CBivariate.ofCoeffRow row)) |
    throw <| IO.userError "normalization failed"
  let candidates ← timed "roots" fun _ ↦ pure (roots.rootsYDegreeLt Q params.interp.messageDegree)
  report s!"root candidates={candidates.size}"
  timed "distance-filter" fun _ ↦
    pure (candidates.filter (passesCandidateDistance w.points params.radius))

private def run {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ofWord : Nat → F) (ctx : GSFilteredCoreContext F) (roots : GSRootContext F)
    (k n e : Nat) (mode fixture : String) : IO Unit := do
  let some params ← timed "selection" fun _ ↦ pure (finiteGSParamSelector.choose k n e) |
    throw <| IO.userError "parameter selection failed"
  report s!"k={k} n={n} e={e} params={repr params} fixture={fixture} mode={mode}"
  let p := CPolynomial.ofArray <| if fixture == "affine" then #[ofWord 7, ofWord 3]
    else (Array.range k).map fun i ↦ ofWord (1234567 + 1664525 * (i + 1))
  let w ← timed "fixture-evaluation" fun _ ↦ pure (GSReceivedWord.mk <|
    (Array.range n).map fun i ↦ let x := ofWord i; (x, CPolynomial.eval x p))
  let result ← timed mode fun _ ↦
    if mode == "profile" then profile roots params w
    else if mode == "roots" then
      pure (roots.rootsYDegreeLt (CBivariate.linearYDivisor p) k)
    else if mode == "normalize" then do
      let some Q ← timed "normalization" fun _ ↦ pure
          (LeeOSullivan.normalizeLeeCandidate? params.interp (CBivariate.linearYDivisor p)) |
        throw <| IO.userError "normalization failed"
      unless CBivariate.composeY Q p == 0 do throw <| IO.userError "invalid normalized witness"
      return #[p]
    else pure (decode ctx finiteGSParamSelector k e w)
  unless result.size == 1 && result.contains p do
    throw <| IO.userError s!"incorrect decoding: {result.size} candidates"
  report s!"validated singleton coefficients={p.val.size}"

/-- Decode an honest row at a production level, or time the decoder's constituent phases.
The dense fixture has all `k` coefficients; the affine fixture isolates setup costs. -/
def main (args : List String) : IO UInt32 := do
  let [level, mode, fixture] := args |
    throw <| IO.userError
      "usage: CompPolyGSBench initial|middle|final profile|decode|roots|normalize affine|dense"
  unless ["profile", "decode", "roots", "normalize"].contains mode do
    throw <| IO.userError "invalid mode"
  unless fixture == "affine" || fixture == "dense" do throw <| IO.userError "invalid fixture"
  if level == "initial" then
    run (fun i ↦ BF64.ofBitVec (BitVec.ofNat 64 i)) BF64.gsFilteredCoreContext
      (rothRuckensteinRootContext BF64 BF64.fieldRootContext) 8192 16384 937 mode fixture
  else if level == "middle" || level == "final" then
    let ofWord := fun i ↦ (CompPoly.Extension.Ext.ofBase
      (BF64.ofBitVec (BitVec.ofNat 64 i)) : BF64.Ext3)
    run ofWord BF64.ext3GSFilteredCoreContext
      (rothRuckensteinRootContext BF64.Ext3 BF64.ext3FieldRootContext)
      (if level == "middle" then 512 else 32) (if level == "middle" then 8192 else 4096)
      (if level == "middle" then 5464 else 3620) mode fixture
  else throw <| IO.userError "invalid level"
  return 0
