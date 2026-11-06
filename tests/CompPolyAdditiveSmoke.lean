/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPolyTests.Fields.Binary.AdditiveNTT.Packed

/-! # Linked packed additive-encoder regression runner -/

public section

/-- Check generic K/E agreement, inverse transforms, layouts and basis conversion. -/
def main : IO Unit := CompPolyTests.Fields.Binary.AdditiveNTT.Packed.runChecks
