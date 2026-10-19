/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Centering.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Coordinate

/-!
# Actual two-coordinate centered lattice target loading

Two actual centered calls read the original supplied coordinates. Their output
views retain the original physical cells, and the third target coordinate is
preserved as supplied. Both native paths come from the same Circuit interpreter.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetPoint

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A structural input avoids every cell written by one centered-coordinate call. -/
def AvoidsTargetWrites {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    {shape : CShape} (input : CInputRef ctx shape) (refs : LatticeTarget.Refs ctx width) :
    Prop :=
  refs.scratch.key ∉ input.storageKeys ∧
    refs.isZero.key ∉ input.storageKeys ∧
      refs.belowHalf.key ∉ input.storageKeys ∧
        refs.output.key ∉ input.storageKeys

/-- Caller-owned data for loading the first two coordinates of one raw target point. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the first stage. -/
  first : LatticeTarget.Refs ctx width
  /-- Nested references for the second stage. -/
  second : LatticeTarget.Refs ctx width
  /-- Nested references for the point stage. -/
  point : LatticeState.PointRefs ctx width
  firstOutput : first.output = point.first
  secondOutput : second.output = point.second

/-- Cross-call separation for the two centered-coordinate routines. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  first : LatticeTarget.Separation refs.first
  second : LatticeTarget.Separation refs.second
  secondAAvoidsFirst : AvoidsTargetWrites refs.second.a refs.first
  secondModulusAvoidsFirst : AvoidsTargetWrites refs.second.modulus refs.first
  secondScratchAvoidsFirst : AvoidsTargetWrites
    (LatticeTarget.writeInput refs.second.scratch) refs.first
  secondIsZeroAvoidsFirst : AvoidsTargetWrites
    (LatticeTarget.writeInput refs.second.isZero) refs.first
  secondBelowHalfAvoidsFirst : AvoidsTargetWrites
    (LatticeTarget.writeInput refs.second.belowHalf) refs.first
  secondOutputAvoidsFirst : AvoidsTargetWrites
    (LatticeTarget.writeInput refs.second.output) refs.first
  firstOutputAvoidsSecond : AvoidsTargetWrites
    (LatticeTarget.writeInput refs.first.output) refs.second
  thirdAvoidsFirst : AvoidsTargetWrites
    (LatticeState.coordinateInput refs.point.third) refs.first
  thirdAvoidsSecond : AvoidsTargetWrites
    (LatticeState.coordinateInput refs.point.third) refs.second

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Execute the two actual centered-coordinate loaders in their original order. -/
def loadTargetPointInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeTarget.centeredTargetInto refs.first)
    (LatticeTarget.centeredTargetInto refs.second)

/-- The actual first call's store feeds the actual second call and both native paths. -/
def targetPointStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (loadTargetPointInto refs).Path :=
  let first := LatticeTarget.centeredTargetStep (model := model) refs.first store
  let second := LatticeTarget.centeredTargetStep (model := model) refs.second first.1
  (second.1, (first.2, second.2))

/-- Both actual coordinate calls retain every state block and incoming history. -/
lemma loadTargetPointInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadTargetPointInto refs).execute environment Reference state
      = state.mapClassical (fun entry =>
      let actual := targetPointStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (LatticeTarget.centeredTargetInto refs.first) (LatticeTarget.centeredTargetInto refs.second)
    (fun before =>
      let actual := LatticeTarget.centeredTargetStep (model := model) refs.first before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeTarget.centeredTargetStep (model := model) refs.second before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeTarget.centeredTargetInto_execute refs.first reference current)
    (fun reference _history _ current =>
      LatticeTarget.centeredTargetInto_execute refs.second reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetPoint
