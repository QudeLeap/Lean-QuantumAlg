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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {coordinateWidth modulusWidth : Nat}

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual original target-power check and first-success selection. -/
def powerSelectionInto (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) : Circuit ctx ctx :=
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
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (powerSelectionInto spec refs).execute Reference state = state.mapClassical (fun entry =>
      ((powerSelectionStep spec refs entry.1).1,
        (entry.2, (powerSelectionStep spec refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeCandidatePowerMachine.candidatePowerInto spec refs.power)
    (LatticeCandidateSelector.candidateSelectorInto refs.selector)
    (LatticeCandidatePowerMachine.candidateStep spec refs.power)
    (LatticeCandidateSelector.selectorStep refs.selector)
    (LatticeCandidatePowerMachine.candidatePowerInto_execute spec refs.power)
    (LatticeCandidateSelector.candidateSelectorInto_execute refs.selector)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual original exponent classification followed by power and selection. -/
def exponentChecksInto (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) : Circuit ctx ctx :=
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
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (exponentChecksInto spec refs).execute Reference state = state.mapClassical (fun entry =>
      ((exponentChecksStep spec refs entry.1).1,
        (entry.2, (exponentChecksStep spec refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeCandidateExponent.candidateExponentInto refs.exponent) (powerSelectionInto spec refs)
    (LatticeCandidateExponent.exponentStep refs.exponent) (powerSelectionStep spec refs)
    (LatticeCandidateExponent.candidateExponentInto_execute refs.exponent)
    (powerSelectionInto_execute spec refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual original distance range check and remaining candidate checks. -/
def rangeChecksInto (spec : ModulusSpec modulusWidth)
    (refs : Refs ctx coordinateWidth modulusWidth) : Circuit ctx ctx :=
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
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (rangeChecksInto spec refs).execute Reference state = state.mapClassical (fun entry =>
      ((rangeChecksStep spec refs entry.1).1,
        (entry.2, (rangeChecksStep spec refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeNearTargetScale.scaleInto refs.nearTarget) (exponentChecksInto spec refs)
    (LatticeNearTargetScale.scaleStep refs.nearTarget) (exponentChecksStep spec refs)
    (LatticeNearTargetScale.scaleInto_execute refs.nearTarget)
    (exponentChecksInto_execute spec refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual original offset, candidate distance and complete candidate checks. -/
def candidateSlotInto (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx coordinateWidth modulusWidth) : Circuit ctx ctx :=
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
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidateSlotInto spec offset refs).execute Reference state = state.mapClassical (fun entry =>
      ((candidateSlotStep spec offset refs entry.1).1,
        (entry.2, (candidateSlotStep spec offset refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeCandidateDistancePrefix.candidateDistancePrefixInto offset refs.distance)
    (rangeChecksInto spec refs)
    (LatticeCandidateDistancePrefix.prefixStep offset refs.distance) (rangeChecksStep spec refs)
    (LatticeCandidateDistancePrefix.candidateDistancePrefixInto_execute offset refs.distance)
    (rangeChecksInto_execute spec refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotMachine
