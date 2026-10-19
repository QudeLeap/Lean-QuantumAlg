/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Prefix
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Numerator
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Execution

/-!
# Actual second-coordinate nearest-plane circuit

The real metric prefix feeds the real numerator, rounded division and target
reduction. Every branch of the division is selected from the actual store;
the complete interpreter equation retains its recorded path.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual metrics, numerator and nearest coefficient drive the second target reduction. -/
def secondInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (secondPrefixInto refs)
    (.seq (numeratorInto refs)
      (.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.second refs.target refs.reduceProduct)))

/-- Actual division and reduction writes, with the selected division path. -/
def divisionReductionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct)).Path :=
  let divided := RoundedDiv.bodyStep refs.division store
  let reduced := LatticeArithmetic.pointStep (writeInput refs.division.output)
    refs.basis.second refs.target refs.reduceProduct divided.1
  (reduced.1, (divided.2, reduced.2))

/-- The numerator's actual store feeds the actual signed division and coordinate updates. -/
def numeratorReductionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (numeratorInto refs)
      (Circuit.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.second refs.target refs.reduceProduct))).Path :=
  let numerator := numeratorStep refs store
  let reduced := divisionReductionStep refs numerator.1
  (reduced.1, (numerator.2, reduced.2))

/-- The complete chronological store and actual selected path of the second phase. -/
def secondStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondInto refs).Path :=
  let loaded := secondPrefixStep refs store
  let reduced := numeratorReductionStep refs loaded.1
  (reduced.1, (loaded.2, reduced.2))

/-- The selected path has the same chronological store as the pure second-phase calculation. -/
lemma secondStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    (secondStep refs store).1 =
      LatticeArithmetic.pointStore (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct
        (RoundedDiv.bodyStep refs.division
          (numeratorStore refs (secondPrefixStore refs store))).1 := rfl

private lemma divisionReduction_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct)).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := divisionReductionStep refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (RoundedDiv.body refs.division)
    (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.second refs.target refs.reduceProduct)
    (fun before =>
      let actual := RoundedDiv.bodyStep refs.division before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeArithmetic.pointStep (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => RoundedDiv.body_execute refs.division reference current)
    (fun reference _history _ current =>
      LatticeArithmetic.pointReduce_execute (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma numeratorReduction_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (numeratorInto refs)
      (Circuit.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.second refs.target refs.reduceProduct))).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := numeratorReductionStep refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment) (numeratorInto refs)
    (.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct))
    (fun before =>
      let actual := numeratorStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := divisionReductionStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => numeratorInto_execute refs reference current)
    (fun reference _history _ current => divisionReduction_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual execution preserves the selected hidden state and reference correlations. -/
lemma secondInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := secondStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment) (secondPrefixInto refs)
    (.seq (numeratorInto refs)
      (.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.second refs.target refs.reduceProduct)))
    (fun before =>
      let actual := secondPrefixStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := numeratorReductionStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => secondPrefixInto_execute refs reference current)
    (fun reference _history _ current => numeratorReduction_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
