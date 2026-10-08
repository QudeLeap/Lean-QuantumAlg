/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word.PowerOfTwo
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual GF(2) pivot-record materialization

The selected row and column use separate lexical masks. Each original
one-hot loader executes self-XOR, increment and the prescribed left shifts.
The row is marked used and written before its mask is released; the column
mask is allocated only afterwards by the caller's sequential composition.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The actual OR instruction that marks a row or column. -/
def pivotOrOp (output mask : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .bitOr width ctx
    (.product (.storage output.toCStorageRef) (.storage mask.toCStorageRef)) output

/-- The actual one-hot row record is written into its selected logical column. -/
def pivotRowWriteOp (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (column : Fin width) :
    ClassicalOp (.product (.fixedVector width (.unsignedWord rowCount)) (.unsignedWord rowCount))
      (.fixedVector width (.unsignedWord rowCount)) ctx ctx :=
  .vectorWrite width rowCount column ctx
    (.product (.storage rows.toCStorageRef) (.storage mask.toCStorageRef)) rows

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Original row-mask loading, used-row update and pivot-row write, in that order. -/
def pivotRowBody (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) : Circuit model ctx ctx :=
  .seq (Word.PowerOfTwo.into (model := model) (rowCount - 1 - pivot.val) mask)
    (.seq (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model) (pivotRowWriteOp rows mask column)))

/-- Original column-mask loading and pivot-column update. -/
def pivotColumnBody (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) : Circuit model ctx ctx :=
  .seq (Word.PowerOfTwo.into (model := model) (width - 1 - column.val) mask)
    (BitWord.instruction (execution := model) (pivotOrOp output mask))

/-- Each mask has a single fresh lexical word, released before the next mask. -/
@[reducible] def pivotMaskContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- The real fresh mask cell inside its lexical scope. -/
def pivotMaskCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (pivotMaskContext ctx width) (.unsignedWord width) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh

/-- Row materialization on the lifted original destinations and actual fresh mask. -/
def placedPivotRow (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) :
    Circuit model (pivotMaskContext ctx rowCount) (pivotMaskContext ctx rowCount) :=
  pivotRowBody (model := model)
    (used.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount) pivot column

/-- Complete original row-mask scope, including its real initialization and release. -/
def materializePivotRow (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord rowCount) ctx.canonicalFreshKey_fresh
    (placedPivotRow (model := model) used rows pivot column)

/-- Column materialization on the lifted original destination and actual fresh mask. -/
def placedPivotColumn (output : CWriteRef ctx (.unsignedWord width)) (column : Fin width) :
    Circuit model (pivotMaskContext ctx width) (pivotMaskContext ctx width) :=
  pivotColumnBody (model := model)
    (output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx width) column

/-- Complete original column-mask scope, independent of the preceding row-mask lifetime. -/
def materializePivotColumn (output : CWriteRef ctx (.unsignedWord width)) (column : Fin width) :
    Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (placedPivotColumn (model := model) output column)

end

end QuantumAlg.ClassicalRoutines.GF2.Native
