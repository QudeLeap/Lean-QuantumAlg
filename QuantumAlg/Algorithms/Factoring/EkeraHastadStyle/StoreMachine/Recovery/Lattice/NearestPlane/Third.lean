/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Prefix
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Sign
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Execution

/-!
# Actual third-coordinate nearest-plane circuit

The real signed denominator is normalized into the existing magnitude word.
Its actual sign controls the numerator correction before actual rounded division
and the third-direction target reduction.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Normalize the actual denominator, correct the numerator, divide and update the target. -/
def thirdNormalizeInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (normalizeMagnitude (writeInput refs.denominator)
      refs.division.negative refs.denominatorMagnitude)
    (.seq (numeratorSignInto refs)
      (.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.third refs.target refs.reduceProduct)))

/-- The actual metric prefix feeds the complete signed third-coordinate reduction. -/
def thirdInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (thirdMetricPrefixInto refs) (thirdNormalizeInto refs)

/-- Actual division writes and target updates, recording the division's actual selected path. -/
def divisionReductionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.third refs.target refs.reduceProduct)).Path :=
  let divided := RoundedDiv.bodyStep refs.division store
  let reduced := LatticeArithmetic.pointStep (writeInput refs.division.output)
    refs.basis.third refs.target refs.reduceProduct divided.1
  (reduced.1, (divided.2, reduced.2))

/-- The actual numerator correction feeds the actual division and coordinate updates. -/
def signReductionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (numeratorSignInto refs)
      (Circuit.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.third refs.target refs.reduceProduct))).Path :=
  let corrected := numeratorSignStep refs store
  let reduced := divisionReductionStep refs corrected.1
  (reduced.1, (corrected.2, reduced.2))

/-- The complete chronological suffix state and its actual normalization and division flags. -/
def thirdNormalizeStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (thirdNormalizeInto refs).Path :=
  let normalized := normalizationStep (writeInput refs.denominator)
    refs.division.negative refs.denominatorMagnitude store
  let reduced := signReductionStep refs normalized.1
  (reduced.1, (normalized.2, reduced.2))

/-- The complete third-phase chronological native updates and selected path. -/
def thirdStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (thirdInto refs).Path :=
  let metrics := metricPrefixStep refs store
  let reduced := thirdNormalizeStep refs metrics.1
  (reduced.1, (metrics.2, reduced.2))

private lemma divisionReduction_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.third refs.target refs.reduceProduct)).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := divisionReductionStep refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (RoundedDiv.body refs.division)
    (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.third refs.target refs.reduceProduct)
    (fun before =>
      let actual := RoundedDiv.bodyStep refs.division before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeArithmetic.pointStep (writeInput refs.division.output)
        refs.basis.third refs.target refs.reduceProduct before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => RoundedDiv.body_execute refs.division reference current)
    (fun reference _history _ current =>
      LatticeArithmetic.pointReduce_execute (writeInput refs.division.output)
        refs.basis.third refs.target refs.reduceProduct reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma signReduction_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (numeratorSignInto refs)
      (Circuit.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.third refs.target refs.reduceProduct))).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := signReductionStep refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment) (numeratorSignInto refs)
    (.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.third refs.target refs.reduceProduct))
    (fun before =>
      let actual := numeratorSignStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := divisionReductionStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => numeratorSignInto_execute refs reference current)
    (fun reference _history _ current => divisionReduction_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The normalization suffix preserves the selected hidden state and reference correlations. -/
lemma thirdNormalizeInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (thirdNormalizeInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := thirdNormalizeStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (normalizeMagnitude (writeInput refs.denominator)
      refs.division.negative refs.denominatorMagnitude)
    (.seq (numeratorSignInto refs)
      (.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.third refs.target refs.reduceProduct)))
    (fun before =>
      let actual := normalizationStep (writeInput refs.denominator)
        refs.division.negative refs.denominatorMagnitude before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := signReductionStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      normalizeMagnitude_execute (writeInput refs.denominator)
        refs.division.negative refs.denominatorMagnitude reference current)
    (fun reference _history _ current => signReduction_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete third-phase execution records all selected branches and incoming correlations. -/
lemma thirdInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (thirdInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := thirdStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment) (thirdMetricPrefixInto refs)
    (thirdNormalizeInto refs)
    (fun before =>
      let actual := metricPrefixStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := thirdNormalizeStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => thirdMetricPrefixInto_execute refs reference current)
    (fun reference _history _ current => thirdNormalizeInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
