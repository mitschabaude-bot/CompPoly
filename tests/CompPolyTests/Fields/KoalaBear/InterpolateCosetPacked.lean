/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.KoalaBear.InterpolateCosetPacked

/-! # Compiled checks of coset interpolation over packed words

`interpolateCosetPacked` runs the packed-storage externs, so these checks are compiled into
`CompPolyNativeSmoke`. Every shape compares it with `interpolateCoset` on the decoded words:
single rows, widths that mix four-column groups with single columns, several blocks and tasks,
words from the modulus up, and malformed byte lengths.
-/

public section
namespace CompPolyTests.Fields.KoalaBear.InterpolateCosetPacked

open CompPoly KoalaBear.Fast Montgomery.Native32

/-- `count` deterministic words, every seventh from the modulus up. -/
def words (seed count : Nat) : Array UInt32 := Id.run do
  let mut out := #[]
  let mut x := seed * 2654435761 + 1
  for i in [:count] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    let w := (x >>> 32) % 2 ^ 32
    out := out.push (if i % 7 == 3 then (2130706433 + w % 2164260863).toUInt32
      else (w % 2130706433).toUInt32)
  return out

def packWords (ws : Array UInt32) : ByteArray :=
  ws.foldl (fun b (w : UInt32) ↦ b.push w.toUInt8 |>.push (w >>> 8).toUInt8
    |>.push (w >>> 16).toUInt8 |>.push (w >>> 24).toUInt8) ByteArray.empty

/-- Compare the packed result with the reference on the words read as residues. -/
def checkShape (logN width : Nat) (ws : Array UInt32) (bytes : ByteArray) (z : Ext4)
    (logTasks : Nat) : IO Unit := do
  let ω := KoalaBear.Fast.twoAdicGenerators.getD logN 0
  let s : Field := ofField 3
  let fields : Array Field := ws.map ofWordMod
  if decodeWords bytes != fields then throw <| IO.userError "word decoding mismatch"
  let fast := interpolateCosetPacked logN ω s width bytes z logTasks
  let reference := interpolateCoset logN ω s width fields z
  if fast != reference then
    throw <| IO.userError s!"packed interpolation mismatch: 2^{logN} × {width}, {bytes.size} bytes"

def run : IO Unit := do
  let z : Ext4 := ⟨ofField 5, ofField 6, ofField 7, ofField 8⟩
  let z' : Ext4 := ⟨ofField 2130706432, ofField 0, ofField 123456789, ofField 1⟩
  for (logN, width) in [(0, 1), (1, 1), (3, 2), (5, 3), (8, 4), (9, 5), (10, 7), (11, 1),
      (12, 9)] do
    let ws := words (logN * 31 + width) (2 ^ logN * width)
    for logTasks in [0, 1, 3] do
      checkShape logN width ws (packWords ws) z logTasks
    checkShape logN width ws (packWords ws) z' 3
  -- Malformed lengths take the reference path.
  checkShape 4 2 (words 1 31) (packWords (words 1 31)) z 3
  checkShape 4 2 (words 2 32) ((packWords (words 2 32)).push 7) z 3
  IO.println "packed coset interpolation: 38 cases agree with the reference"

end CompPolyTests.Fields.KoalaBear.InterpolateCosetPacked
