/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual GF(2) pivot-record candidate construction

The actual pivot record controls each row contribution. A selected row
allocates its masked word and equality bit, reads the real reduced row,
and allocates the original one-hot column mask only when equality rejects.
The existing real column materializer supplies that one-hot/OR scope.
Construction first copies the free mask, then traverses columns before rows.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The original free mask is copied into the real candidate before any row contributions. -/
def candidateCopyOp (free candidate : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (.storage free.toCStorageRef) candidate

/-- The original structural row operand is ANDed with the current free mask. -/
def candidateMaskOp (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free work : CWriteRef ctx (.unsignedWord width)) (row : Fin rowCount) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .bitAnd width ctx
    (.product (.vectorGet (.storage matrix.toCStorageRef) row) (.storage free.toCStorageRef)) work

/-- The original nonzero coefficient branch performs the actual one-hot/OR scope. -/
def candidateCoefficientChoice (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) : CShape.Value .bit → Circuit ctx ctx
  | .bit false => materializePivotColumn candidate column
  | .bit true => .id ctx

/-- The reduced row is masked and compared before the actual coefficient branch. -/
def candidateRowBody (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width) : Circuit ctx ctx :=
  .seq (.classical (candidateMaskOp matrix free work row))
    (.seq (.classical (decisionEqualityOp work zero flag))
      (.branch (.storage flag.toCStorageRef) (candidateCoefficientChoice candidate column)))

/-- The selected row runs below its actual masked word and equality flag. -/
def placedCandidateRow (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) :
    Circuit (decisionContext ctx width) (decisionContext ctx width) :=
  candidateRowBody (decisionWrite width matrix) (decisionWrite width free)
    (decisionWrite width candidate) (decisionWrite width zero) (decisionWork ctx width)
    (pivotLatch (pivotMaskContext ctx width)) row column

/-- The original equality bit is released before the masked row word. -/
def scopedCandidateRow (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) :
    Circuit (pivotMaskContext ctx width) (pivotMaskContext ctx width) :=
  .workspace (pivotMaskContext ctx width) (pivotMaskContext ctx width).canonicalFreshKey
    .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
      (placedCandidateRow matrix free candidate zero row column)

/-- A selected pivot record enters both original scopes before evaluating its coefficient. -/
def candidateRowSelected (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (scopedCandidateRow matrix free candidate zero row column)

/-- The actual pivot-record bit selects its original row contribution or identity. -/
def candidatePivotChoice (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) : CShape.Value .bit → Circuit ctx ctx
  | .bit false => .id ctx
  | .bit true => candidateRowSelected matrix free candidate zero row column

/-- The original MSB-first column-to-row pivot record controls each contribution. -/
def candidatePivotRow (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) : Circuit ctx ctx :=
  .branch (eliminationBit rows column row)
    (candidatePivotChoice matrix free candidate zero row column)

/-- The original free-mask copy is followed by increasing columns and then increasing rows. -/
def buildCandidate (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (candidateCopyOp free candidate))
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column)))

end QuantumAlg.ClassicalRoutines.GF2.Native
