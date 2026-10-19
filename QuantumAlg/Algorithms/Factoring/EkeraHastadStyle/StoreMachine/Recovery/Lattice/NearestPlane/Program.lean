/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Program.Layout

/-!
# Actual complete three-stage nearest-plane circuit

Third, second and first coordinate reductions share the actual residual target.
Each phase receives the preceding phase's real store and records its own actual
branch path in the same circuit interpreter.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Execute the actual third, second and first nearest-plane reductions in order. -/
def threeInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeNearestPlaneThird.thirdInto (thirdRefs refs))
    (.seq (LatticeNearestPlaneSecond.secondInto (secondRefs refs))
      (LatticeNearestPlaneFirst.firstInto (firstRefs refs)))

/-- Actual second and first stage stores and their two selected paths. -/
def secondFirstStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (LatticeNearestPlaneSecond.secondInto (secondRefs refs))
      (LatticeNearestPlaneFirst.firstInto (firstRefs refs))).Path :=
  let second := LatticeNearestPlaneSecond.secondStep (secondRefs refs) store
  let first := LatticeNearestPlaneFirst.firstStep (firstRefs refs) second.1
  (first.1, (second.2, first.2))

/-- Complete chronological stores and actual path of all three reductions. -/
def threeStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (threeInto refs).Path :=
  let third := LatticeNearestPlaneThird.thirdStep (thirdRefs refs) store
  let rest := secondFirstStep refs third.1
  (rest.1, (third.2, rest.2))

private lemma secondFirst_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (LatticeNearestPlaneSecond.secondInto (secondRefs refs))
      (LatticeNearestPlaneFirst.firstInto (firstRefs refs))).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := secondFirstStep refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (LatticeNearestPlaneSecond.secondInto (secondRefs refs))
    (LatticeNearestPlaneFirst.firstInto (firstRefs refs))
    (fun before =>
      let actual := LatticeNearestPlaneSecond.secondStep (secondRefs refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeNearestPlaneFirst.firstStep (firstRefs refs) before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeNearestPlaneSecond.secondInto_execute (secondRefs refs) reference current)
    (fun reference _history _ current =>
      LatticeNearestPlaneFirst.firstInto_execute (firstRefs refs) reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual execution preserves the selected hidden state and reference correlations. -/
lemma threeInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (threeInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := threeStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (LatticeNearestPlaneThird.thirdInto (thirdRefs refs))
    (.seq (LatticeNearestPlaneSecond.secondInto (secondRefs refs))
      (LatticeNearestPlaneFirst.firstInto (firstRefs refs)))
    (fun before =>
      let actual := LatticeNearestPlaneThird.thirdStep (thirdRefs refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := secondFirstStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeNearestPlaneThird.thirdInto_execute (thirdRefs refs) reference current)
    (fun reference _history _ current => secondFirst_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual third phase preserves every read outside its written footprint. -/
lemma thirdInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : ThirdFrameAvoids refs other) :
    (LatticeNearestPlaneThird.thirdStep (thirdRefs refs) store).1.read other = store.read other :=
  LatticeNearestPlaneThird.thirdInto_callerFrame (thirdRefs refs) store other avoids

/-- The actual second phase preserves every read outside its written footprint. -/
lemma secondInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : SecondFrameAvoids refs other) :
    (LatticeNearestPlaneSecond.secondStep (secondRefs refs) store).1.read other =
      store.read other :=
  LatticeNearestPlaneSecond.secondInto_callerFrame (secondRefs refs) store other avoids

/-- The actual first phase preserves every read outside its written footprint. -/
lemma firstInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : FirstFrameAvoids refs other) :
    (LatticeNearestPlaneFirst.firstStep (firstRefs refs) store).1.read other = store.read other :=
  LatticeNearestPlaneFirst.firstInto_callerFrame (firstRefs refs) store other
    avoids.dotProduct avoids.numerator avoids.normProduct avoids.denominator avoids.division
    avoids.reduceProduct avoids.targetFirst avoids.targetSecond avoids.targetThird

/-- All three actual stages preserve every read outside their combined written footprint. -/
lemma threeInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : FrameAvoids refs other) :
    (threeStep refs store).1.read other = store.read other := by
  unfold threeStep secondFirstStep
  rw [firstInto_callerFrame refs _ other avoids.first,
    secondInto_callerFrame refs _ other avoids.second,
    thirdInto_callerFrame refs store other avoids.third]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree
