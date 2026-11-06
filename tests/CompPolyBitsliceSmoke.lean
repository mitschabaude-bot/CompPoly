/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
import CompPolyTests.Fields.Binary.AdditiveNTT.Bitsliced
/-! # Linked bit-plane encoder regressions -/
public section
/-- Check transposes, scalar matrices, packed agreement and inverse encoding. -/
def main : IO Unit := CompPolyTests.Fields.Binary.AdditiveNTT.Bitsliced.runChecks
