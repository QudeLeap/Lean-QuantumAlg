/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Load
import all QuantumAlg.Components.Classical.GF2.Native.Pivot

/-!
# Actual complete GF(2) matrix-reduction prefix

The original used-row and pivot-column self-XORs precede the real pivot-row
initialization. A single fresh zero row word supplies every initialization
write. Increasing column order then runs the existing actual pivot search.
The four resulting caller cells remain live for the original later candidate
construction, validation and optional output packing; those later stages are
not replaced by a mathematical output in this prefix.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The original ordered pivot-row writes share the same actual zero-word source. -/
def pivotRowsClearBody (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) : Circuit ctx ctx :=
  Circuit.forRange width (fun column => .classical (pivotRowWriteOp rows zero column))

/-- The fresh row word is the real initializer of every pivot-row record. -/
def placedPivotRowsClear (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount))) :
    Circuit (pivotMaskContext ctx rowCount) (pivotMaskContext ctx rowCount) :=
  pivotRowsClearBody
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount)

/-- Allocate one real zero row word, perform all original vector writes, then release it. -/
def clearPivotRows (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount))) :
    Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord rowCount) ctx.canonicalFreshKey_fresh
    (placedPivotRowsClear rows)

/-- The original three initializations precede the complete increasing column traversal. -/
def reduceMatrix (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (Word.PowerOfTwo.clearOp used))
    (.seq (.classical (Word.PowerOfTwo.clearOp columns))
      (.seq (clearPivotRows rows)
        (Circuit.forRange width (reduceColumn matrix used rows columns))))

/-- The exact original loading and reduction prefix leaves its four actual output cells live. -/
def loadAndReduce (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (loadMatrix input matrix) (reduceMatrix matrix used rows columns)

end QuantumAlg.ClassicalRoutines.GF2.Native
