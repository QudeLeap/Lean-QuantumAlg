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

/-- Execute the two actual centered-coordinate loaders in their original order. -/
def loadTargetPointInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeTarget.centeredTargetInto refs.first)
    (LatticeTarget.centeredTargetInto refs.second)

/-- The actual first call's store feeds the actual second call and both native paths. -/
def targetPointStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (loadTargetPointInto refs).Path :=
  let first := LatticeTarget.centeredTargetStep refs.first store
  let second := LatticeTarget.centeredTargetStep refs.second first.1
  (second.1, (first.2, second.2))

/-- Both actual coordinate calls retain every state block and incoming history. -/
theorem loadTargetPointInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (loadTargetPointInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((targetPointStep refs entry.1).1, (entry.2, (targetPointStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeTarget.centeredTargetInto refs.first) (LatticeTarget.centeredTargetInto refs.second)
    (LatticeTarget.centeredTargetStep refs.first) (LatticeTarget.centeredTargetStep refs.second)
    (LatticeTarget.centeredTargetInto_execute refs.first)
    (LatticeTarget.centeredTargetInto_execute refs.second) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTargetPoint
