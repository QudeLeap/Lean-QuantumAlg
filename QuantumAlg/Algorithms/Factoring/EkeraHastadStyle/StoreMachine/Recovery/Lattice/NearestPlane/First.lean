/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.First.Layout
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Execution

/-!
# Actual first-coordinate nearest-plane circuit

The real dot and norm refreshes feed signed nearest division, whose stored
coefficient drives the actual coordinate updates. The full interpreter equation
records that coefficient's real branch history and every chronological store.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Four actual stages compute the nearest coefficient and update the residual target. -/
def firstInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeDotRefresh.refreshInto refs.target refs.basis.first (numeratorDotRefs refs))
    (.seq (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
      (.seq (SignedWord.RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
          refs.basis.first refs.target refs.reduceProduct)))

/-- Actual division writes and coordinate writes, with the division's selected path. -/
def divisionReductionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (SignedWord.RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct)).Path :=
  let divided := SignedWord.RoundedDiv.bodyStep refs.division store
  let reduced := LatticeArithmetic.pointStep (SignedWord.writeInput refs.division.output)
    refs.basis.first refs.target refs.reduceProduct divided.1
  (reduced.1, (divided.2, reduced.2))

/-- Norm refresh feeds its actual resulting store into division and reduction. -/
def normReductionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq
      (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
      (Circuit.seq (SignedWord.RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
          refs.basis.first refs.target refs.reduceProduct))).Path :=
  let normed := LatticeDotRefresh.refreshStep refs.basis.first refs.basis.first
    (LatticeNormRefresh.dotRefs (denominatorNormRefs refs)) store
  let reduced := divisionReductionStep refs normed.1
  (reduced.1, (normed.2, reduced.2))

/-- Complete chronological native updates and actual selected path of the first phase. -/
def firstStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (firstInto refs).Path :=
  let dotted := LatticeDotRefresh.refreshStep refs.target refs.basis.first
    (numeratorDotRefs refs) store
  let reduced := normReductionStep refs dotted.1
  (reduced.1, (dotted.2, reduced.2))

/-- The selected path has the chronological pure first-phase store. -/
lemma firstStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    (firstStep refs store).1 =
      LatticeArithmetic.pointStore (writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct
        (SignedWord.RoundedDiv.bodyStep refs.division
          (LatticeNormRefresh.refreshStore refs.basis.first (denominatorNormRefs refs)
            (LatticeDotRefresh.refreshStore refs.target refs.basis.first
              (numeratorDotRefs refs) store))).1 := rfl

private lemma divisionReduction_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (SignedWord.RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct)).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := divisionReductionStep refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (SignedWord.RoundedDiv.body refs.division)
    (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.first refs.target refs.reduceProduct)
    (fun before =>
      let actual := SignedWord.RoundedDiv.bodyStep refs.division before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeArithmetic.pointStep (writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => SignedWord.RoundedDiv.body_execute
      refs.division reference current)
    (fun reference _history _ current =>
      LatticeArithmetic.pointReduce_execute (writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma normReduction_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq
      (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
      (Circuit.seq (SignedWord.RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
          refs.basis.first refs.target refs.reduceProduct))).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := normReductionStep refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
    (.seq (SignedWord.RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct))
    (fun before =>
      let actual := LatticeDotRefresh.refreshStep refs.basis.first refs.basis.first
        (LatticeNormRefresh.dotRefs (denominatorNormRefs refs)) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := divisionReductionStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeNormRefresh.refreshInto_execute refs.basis.first (denominatorNormRefs refs)
        reference current)
    (fun reference _history _ current => divisionReduction_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual execution preserves the selected hidden state and reference correlations. -/
lemma firstInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (firstInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := firstStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (LatticeDotRefresh.refreshInto refs.target refs.basis.first (numeratorDotRefs refs))
    (.seq (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
      (.seq (SignedWord.RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.first refs.target refs.reduceProduct)))
    (fun before =>
      let actual := LatticeDotRefresh.refreshStep refs.target refs.basis.first
        (numeratorDotRefs refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := normReductionStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeDotRefresh.refreshInto_execute refs.target refs.basis.first
        (numeratorDotRefs refs) reference current)
    (fun reference _history _ current => normReduction_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst
