/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Swap.Coordinate

/-!
# Actual nine-copy lattice row exchange

Three actual coordinate exchanges share one caller-owned scratch word. The
complete actual store and path retain all nine native copy operations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Execute the three original coordinate exchanges through the same actual scratch word. -/
def pointSwap {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (coordinateSwap left.first right.first scratch)
    (.seq (coordinateSwap left.second right.second scratch)
      (coordinateSwap left.third right.third scratch))

/-- The actual chronological stores after all three coordinate exchanges. -/
def pointSwapStore (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  coordinateSwapStore left.third right.third scratch
    (coordinateSwapStore left.second right.second scratch
      (coordinateSwapStore left.first right.first scratch store))

/-- Actual three-coordinate exchange stores and selected operation paths. -/
def pointSwapStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (pointSwap (model := model) left right scratch).Path :=
  let first := coordinateSwapStep (model := model) left.first right.first scratch store
  let second := coordinateSwapStep (model := model) left.second right.second scratch first.1
  let third := coordinateSwapStep (model := model) left.third right.third scratch second.1
  (third.1, (first.2, (second.2, third.2)))

lemma pointSwapStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (pointSwapStep (model := model) left right scratch store).1 =
      pointSwapStore left right scratch store := rfl

/-- Full actual execution preserves history and all quantum-reference blocks. -/
lemma pointSwap_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pointSwap (model := model) left right scratch).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := pointSwapStep (model := model) left right scratch entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [pointSwap, pointSwapStep, Circuit.execute_seq, coordinateSwap_execute,
    State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Any caller read outside the full seven-cell actual footprint is preserved. -/
lemma pointSwap_callerFrame (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell, pointSwapCellKey left right scratch cell ∉ other.storageKeys) :
    (pointSwapStore left right scratch store).read other = store.read other := by
  unfold pointSwapStore
  rw [coordinateSwap_callerFrame _ _ _ _ other
    (avoids .leftThird) (avoids .rightThird) (avoids .scratch),
    coordinateSwap_callerFrame _ _ _ _ other
      (avoids .leftSecond) (avoids .rightSecond) (avoids .scratch),
    coordinateSwap_callerFrame _ _ _ _ other
      (avoids .leftFirst) (avoids .rightFirst) (avoids .scratch)]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap
