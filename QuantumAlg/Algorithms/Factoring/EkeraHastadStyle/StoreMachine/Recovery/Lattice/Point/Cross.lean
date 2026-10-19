/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Cross.Coordinate

/-!
# Actual three-dimensional cross product

Six native low-word multiplications and three subtractions produce the three
independent output coordinates. The two product words are reused in sequence.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual cross product, in first, second and third coordinate order. -/
def pointCrossInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (coordinateCross (writeInput left.second) (writeInput right.third)
      (writeInput left.third) (writeInput right.second) output.first productLeft productRight)
    (.seq (coordinateCross (writeInput left.third) (writeInput right.first)
        (writeInput left.first) (writeInput right.third) output.second productLeft productRight)
      (coordinateCross (writeInput left.first) (writeInput right.second)
        (writeInput left.second) (writeInput right.first) output.third productLeft productRight))

/-- The nine chronological native writes of the actual point circuit. -/
def pointStore (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx :=
  coordinateStore (writeInput left.first) (writeInput right.second)
    (writeInput left.second) (writeInput right.first) output.third productLeft productRight
    (coordinateStore (writeInput left.third) (writeInput right.first)
      (writeInput left.first) (writeInput right.third) output.second productLeft productRight
      (coordinateStore (writeInput left.second) (writeInput right.third)
        (writeInput left.third) (writeInput right.second) output.first productLeft productRight
        store))

/-- The nine actual writes and their selected chronological operation paths. -/
def pointStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (pointCrossInto (model := model) left right output productLeft productRight).Path :=
  let first := coordinateStep (model := model)
    (writeInput left.second) (writeInput right.third)
    (writeInput left.third) (writeInput right.second)
    output.first productLeft productRight store
  let second := coordinateStep (model := model)
    (writeInput left.third) (writeInput right.first)
    (writeInput left.first) (writeInput right.third)
    output.second productLeft productRight first.1
  let third := coordinateStep (model := model)
    (writeInput left.first) (writeInput right.second)
    (writeInput left.second) (writeInput right.first)
    output.third productLeft productRight second.1
  (third.1, (first.2, (second.2, third.2)))

lemma pointStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (pointStep (model := model) left right output productLeft productRight store).1 =
      pointStore left right output productLeft productRight store := rfl

/-- The full interpreter retains every incoming history and quantum-reference block. -/
lemma pointCrossInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pointCrossInto (model := model) left right output productLeft productRight).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        let actual := pointStep (model := model) left right output productLeft productRight
          entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [pointCrossInto, pointStep, Circuit.execute_seq, coordinateCross_execute,
    State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Reads outside the five mutable words are unchanged. -/
lemma pointCrossInto_callerFrame (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell, mutableKey output productLeft productRight cell ∉ other.storageKeys) :
    (pointStore left right output productLeft productRight store).read other =
      store.read other := by
  unfold pointStore
  rw [coordinateCross_callerFrame _ _ _ _ _ _ _ _ other
      (avoids .outputThird) (avoids .productLeft) (avoids .productRight),
    coordinateCross_callerFrame _ _ _ _ _ _ _ _ other
      (avoids .outputSecond) (avoids .productLeft) (avoids .productRight),
    coordinateCross_callerFrame _ _ _ _ _ _ _ _ other
      (avoids .outputFirst) (avoids .productLeft) (avoids .productRight)]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross
