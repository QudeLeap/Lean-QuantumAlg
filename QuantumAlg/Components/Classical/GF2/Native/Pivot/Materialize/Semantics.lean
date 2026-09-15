/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Complete records of actual pivot-mask materialization

Each record follows the real power loader, bitwise OR and optional vector
write on its intermediate store. Both lexical exits preserve the complete
caller store, reference and history through those actual records.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The real row-mask loader is followed by both original writes on their intermediate stores. -/
def pivotRowBodyStep (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (store : Store ctx) :
    Store ctx × (pivotRowBody used rows mask pivot column).Path :=
  Circuit.sequenceRecord (Word.PowerOfTwo.into (rowCount - 1 - pivot.val) mask)
    (.seq (.classical (pivotOrOp used mask)) (.classical (pivotRowWriteOp rows mask column)))
    (Word.PowerOfTwo.step (rowCount - 1 - pivot.val) mask)
    (Circuit.sequenceRecord (.classical (pivotOrOp used mask))
      (.classical (pivotRowWriteOp rows mask column))
      (fun current => (current.applyOp (pivotOrOp used mask), ()))
      (fun current => (current.applyOp (pivotRowWriteOp rows mask column), ()))) store

/-- Every original row-materialization instruction acts on the complete actual state. -/
theorem gf2PivotRowBody_execute (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (pivotRowBody used rows mask pivot column).execute Reference state =
      state.mapClassical (fun entry =>
        ((pivotRowBodyStep used rows mask pivot column entry.1).1,
          (entry.2, (pivotRowBodyStep used rows mask pivot column entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _
    (Word.PowerOfTwo.into_execute _ _)
    (Circuit.execute_sequenceRecord _ _ _ _
      (fun reference {_} _ current => by
        refine (Circuit.execute_classical_mapClassical (pivotOrOp used mask)
          reference current).trans ?_
        congr 1
        exact Subsingleton.elim _ _)
      (fun reference {_} _ current => by
        refine (Circuit.execute_classical_mapClassical (pivotRowWriteOp rows mask column)
          reference current).trans ?_
        congr 1
        exact Subsingleton.elim _ _)) Reference state

/-- Actual row materialization starts with its fresh mask and pops it only after both writes. -/
def materializePivotRowStep (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (materializePivotRow used rows pivot column).Path :=
  let actual := pivotRowBodyStep
    (used.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount) pivot column
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The full row-mask scope maps arbitrary original store/reference/history correlations. -/
theorem gf2MaterializePivotRow_execute (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (materializePivotRow used rows pivot column).execute Reference state =
      state.mapClassical (fun entry =>
        ((materializePivotRowStep used rows pivot column entry.1).1,
          (entry.2, (materializePivotRowStep used rows pivot column entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (gf2PivotRowBody_execute _ _ _ pivot column) Reference state

/-- The column-mask record retains the actual loader path and its original OR instruction. -/
def pivotColumnBodyStep (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (store : Store ctx) :
    Store ctx × (pivotColumnBody output mask column).Path :=
  Circuit.sequenceRecord (Word.PowerOfTwo.into (width - 1 - column.val) mask)
    (.classical (pivotOrOp output mask)) (Word.PowerOfTwo.step (width - 1 - column.val) mask)
    (fun current => (current.applyOp (pivotOrOp output mask), ())) store

/-- Both original column-materialization stages preserve all complete quantum-reference blocks. -/
theorem gf2PivotColumnBody_execute (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (pivotColumnBody output mask column).execute Reference state =
      state.mapClassical (fun entry =>
        ((pivotColumnBodyStep output mask column entry.1).1,
          (entry.2, (pivotColumnBodyStep output mask column entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (Word.PowerOfTwo.into_execute _ _)
    (fun reference {_} _ current => by
      refine (Circuit.execute_classical_mapClassical (pivotOrOp output mask)
        reference current).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state

/-- The column mask is allocated and popped independently of the completed row-mask scope. -/
def materializePivotColumnStep (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (store : Store ctx) :
    Store ctx × (materializePivotColumn output column).Path :=
  let actual := pivotColumnBodyStep
    (output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx width) column
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- Column materialization has the complete original-store/reference execution equation. -/
theorem gf2MaterializePivotColumn_execute (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (materializePivotColumn output column).execute Reference state =
      state.mapClassical (fun entry =>
        ((materializePivotColumnStep output column entry.1).1,
          (entry.2, (materializePivotColumnStep output column entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (gf2PivotColumnBody_execute _ _ column) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
