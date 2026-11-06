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
  let V := CPolynomial.VanishingPolynomialContext.subproduct (BF64.structuredMulContext F)
  let E := CPolynomial.BatchEvalContext.subproduct F (BF64.structuredMulContext F)
    CPolynomial.ModContext.remainderOnly
  let G ← timed "vanishing" fun _ ↦ pure (V.vanishingPolynomial (w.points.map Prod.fst))
  report s!"vanishing coefficients={G.val.size}"
  let R ← timed "coefficient-interpolation" fun _ ↦ do
    let derivative ← timed "derivative" fun _ ↦ pure (CPolynomial.derivative G)
    let values ← timed "derivative-evaluation" fun _ ↦
      pure (E.evalBatchWith derivative (w.points.map Prod.fst))
    timed "interpolation-assembly" fun _ ↦ pure <|
      (List.range w.points.size).foldl (fun acc i ↦
        acc + CPolynomial.interpolationTermWithVanishing G
          (w.points.getD i (0, 0)) (values.getD i 0)) 0
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
    (ofWord ofCoefficient : Nat → F) (ctx : GSFilteredCoreContext F) (roots : GSRootContext F)
    (k n e : Nat) (mode fixture : String) : IO Unit := do
  let some params ← timed "selection" fun _ ↦ pure (finiteGSParamSelector.choose k n e) |
    throw <| IO.userError "parameter selection failed"
  report s!"k={k} n={n} e={e} params={repr params} fixture={fixture} mode={mode}"
  let a := ofCoefficient 7
  let b := ofCoefficient 3
  let c := ofCoefficient 0x9e3779b97f4a7c15
  let p := CPolynomial.ofArray <| if fixture == "affine" then #[a, b]
    else ((Array.replicate k c).set! 0 (c + a)).set! 1 (c + b)
  -- For power-of-two k in characteristic two, (X + 1)^(k - 1) has every coefficient one.
  let value := fun x ↦ if fixture == "affine" then CPolynomial.eval x p
    else c * (x + 1) ^ (k - 1) + a + b * x
  let _ ← timed "fixture-validation" fun _ ↦ do
    for i in [0:4] do
      let x := ofWord i
      unless value x == CPolynomial.eval x p do
        throw <| IO.userError "dense fixture identity failed"
  let w ← timed "fixture-evaluation" fun _ ↦ pure (GSReceivedWord.mk <|
    (Array.range n).map fun i ↦ let x := ofWord i; (x, value x))
  let result ← timed mode fun _ ↦
    if mode == "profile" then profile roots params w
    else if mode == "roots" then
      pure (roots.rootsYDegreeLt (CBivariate.linearYDivisor p) k)
    else if mode == "normalize" || mode == "normalize-phases" then do
      let rawQ := CBivariate.linearYDivisor p
      let some Q ← if mode == "normalize" then
          timed "normalization" fun _ ↦
            pure (LeeOSullivan.normalizeLeeCandidate? params.interp rawQ)
        else do
          let basis ← timed "monomial-enumeration" fun _ ↦
            pure (interpolationMonomials params.interp)
          report s!"monomials={basis.size}"
          let coeffs ← timed "coefficient-vector" fun _ ↦
            pure (interpolationCoefficientVectorOnBasis basis rawQ)
          let some normalized ← timed "vector-normalization" fun _ ↦
              pure (normalizeVector? coeffs) |
            throw <| IO.userError "vector normalization failed"
          timed "polynomial-reconstruction" fun _ ↦
            pure (some (interpolationPolynomialOnBasis basis normalized)) |
        throw <| IO.userError "normalization failed"
      unless CBivariate.composeY Q p == 0 do throw <| IO.userError "invalid normalized witness"
      return #[p]
    else pure (decode ctx finiteGSParamSelector k e w)
  unless result.size == 1 && result.contains p do
    throw <| IO.userError s!"incorrect decoding: {result.size} candidates"
  report s!"validated singleton coefficients={p.val.size}"

/-- Decode an honest row at a production level, or time the decoder's constituent phases.
The dense fixture is a geometric sum plus an affine term, with all `k` coefficients.
The affine fixture isolates setup costs. -/
def main (args : List String) : IO UInt32 := do
  let [level, mode, fixture] := args |
    throw <| IO.userError
      ("usage: CompPolyGSBench initial|middle|final " ++
        "profile|decode|roots|normalize|normalize-phases affine|dense")
  unless ["profile", "decode", "roots", "normalize", "normalize-phases"].contains mode do
    throw <| IO.userError "invalid mode"
  unless fixture == "affine" || fixture == "dense" do throw <| IO.userError "invalid fixture"
  if level == "initial" then
    let ofWord := fun i ↦ BF64.ofBitVec (BitVec.ofNat 64 i)
    run ofWord ofWord BF64.gsFilteredCoreContext
      (rothRuckensteinRootContext BF64 BF64.fieldRootContext) 8192 16384 937 mode fixture
  else if level == "middle" || level == "final" then
    let ofWord := fun i ↦ (CompPoly.Extension.Ext.ofBase
      (BF64.ofBitVec (BitVec.ofNat 64 i)) : BF64.Ext3)
    let ofCoefficient := fun i ↦ (CompPoly.Extension.Ext.ofFn fun j ↦
      BF64.ofBitVec (BitVec.ofNat 64 (i * (2 * j.val + 1) + 17 * j.val)) : BF64.Ext3)
    run ofWord ofCoefficient BF64.ext3GSFilteredCoreContext
      (rothRuckensteinRootContext BF64.Ext3 BF64.ext3FieldRootContext)
      (if level == "middle" then 512 else 32) (if level == "middle" then 8192 else 4096)
      (if level == "middle" then 5464 else 3620) mode fixture
  else throw <| IO.userError "invalid level"
  return 0
