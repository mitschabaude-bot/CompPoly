/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.KoalaBear.FastExt5
public import CompPoly.Fields.Montgomery.Native32ExtPlanesCorrectness

/-!
# Coordinate planes of KoalaBear's quintic extension

`KoalaBear.Fast.Ext5` inverts its coordinate planes by Montgomery's batch inversion of the
elements (`PlanesInv.ofBatch`), which measured faster than the Frobenius norm on planes.
-/

@[expose] public section

namespace KoalaBear.Fast.Ext5

open Montgomery.Native32

/-- The quintic extension inverts planes by batch inversion. -/
@[inline] instance instPlanesInv : PlanesInv KoalaBear.fieldSize Ext5 := PlanesInv.ofBatch

end KoalaBear.Fast.Ext5
