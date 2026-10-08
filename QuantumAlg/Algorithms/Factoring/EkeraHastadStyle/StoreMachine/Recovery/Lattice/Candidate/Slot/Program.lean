/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Layout

/-!
# Actual complete candidate-slot execution
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotMachine

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {coordinateWidth modulusWidth : Nat}

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual original target-power check and first-success selection. -/
def powerSelectionInto (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) : Circuit model ctx ctx :=
  .seq (LatticeCandidatePowerMachine.candidatePowerInto spec refs.power)
    (LatticeCandidateSelector.candidateSelectorInto refs.selector)

/-- Complete chronological store and selected paths of the actual original target-power check
and first-success selection. -/
def powerSelectionStep (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) (store : Store ctx) :
    Store ctx × (powerSelectionInto spec refs).Path :=
  let first := LatticeCandidatePowerMachine.candidateStep spec refs.power store
  let second := LatticeCandidateSelector.selectorStep refs.selector first.1
  (second.1, (first.2, second.2))

/-- The actual original target-power check and first-success selection retain every incoming
quantum-reference block. -/
theorem powerSelectionInto_execute (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (powerSelectionInto spec refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := powerSelectionStep spec refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [powerSelectionInto, Circuit.execute_seq,
    LatticeCandidatePowerMachine.candidatePowerInto_execute,
    LatticeCandidateSelector.candidateSelectorInto_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual original exponent classification followed by power and selection. -/
def exponentChecksInto (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) : Circuit model ctx ctx :=
  .seq (LatticeCandidateExponent.candidateExponentInto refs.exponent) (powerSelectionInto spec refs)

/-- Complete chronological store and selected paths of the actual original exponent
classification followed by power and selection. -/
def exponentChecksStep (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) (store : Store ctx) :
    Store ctx × (exponentChecksInto spec refs).Path :=
  let first := LatticeCandidateExponent.exponentStep refs.exponent store
  let second := powerSelectionStep spec refs first.1
  (second.1, (first.2, second.2))

/-- The actual original exponent classification followed by power and selection retain every
incoming quantum-reference block. -/
theorem exponentChecksInto_execute (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (exponentChecksInto spec refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := exponentChecksStep spec refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [exponentChecksInto, Circuit.execute_seq,
    LatticeCandidateExponent.candidateExponentInto_execute, powerSelectionInto_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual original distance range check and remaining candidate checks. -/
def rangeChecksInto (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) : Circuit model ctx ctx :=
  .seq (LatticeNearTargetScale.scaleInto refs.nearTarget) (exponentChecksInto spec refs)

/-- Complete chronological store and selected paths of the actual original distance range
check and remaining candidate checks. -/
def rangeChecksStep (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) (store : Store ctx) :
    Store ctx × (rangeChecksInto spec refs).Path :=
  let first := LatticeNearTargetScale.scaleStep refs.nearTarget store
  let second := exponentChecksStep spec refs first.1
  (second.1, (first.2, second.2))

/-- The actual original distance range check and remaining candidate checks retain every
incoming quantum-reference block. -/
theorem rangeChecksInto_execute (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (rangeChecksInto spec refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := rangeChecksStep spec refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [rangeChecksInto, Circuit.execute_seq,
    LatticeNearTargetScale.scaleInto_execute, exponentChecksInto_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual original offset, candidate distance and complete candidate checks. -/
def candidateSlotInto (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx coordinateWidth modulusWidth) : Circuit model ctx ctx :=
  .seq (LatticeCandidateDistancePrefix.candidateDistancePrefixInto offset refs.distance)
    (rangeChecksInto spec refs)

/-- Complete chronological store and selected paths of the actual original offset, candidate
distance and complete candidate checks. -/
def candidateSlotStep (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx coordinateWidth modulusWidth) (store : Store ctx) :
    Store ctx × (candidateSlotInto spec offset refs).Path :=
  let first := LatticeCandidateDistancePrefix.prefixStep offset refs.distance store
  let second := rangeChecksStep spec refs first.1
  (second.1, (first.2, second.2))

/-- The actual original offset, candidate distance and complete candidate checks retain every
incoming quantum-reference block. -/
theorem candidateSlotInto_execute (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx coordinateWidth modulusWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (candidateSlotInto spec offset refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := candidateSlotStep spec offset refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [candidateSlotInto, Circuit.execute_seq,
    LatticeCandidateDistancePrefix.candidateDistancePrefixInto_execute,
    rangeChecksInto_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotMachine
