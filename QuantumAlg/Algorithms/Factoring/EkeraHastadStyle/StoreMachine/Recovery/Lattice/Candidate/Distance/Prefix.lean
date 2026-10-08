/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Distance.Prefix.Layout

/-!
# Actual original offset, candidate and distance composition
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateDistancePrefix

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual candidate-point construction precedes explicit initialized squared-distance work. -/
def candidateDistanceInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeShortLogCandidatePoint.candidatePointInto refs.candidate)
    (LatticeSquaredDistanceMachine.squaredDistanceInto refs.distance)

/-- Actual chronological candidate and distance stores with both native paths. -/
def candidateDistanceStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidateDistanceInto refs).Path :=
  let candidate := LatticeShortLogCandidatePoint.candidateStep refs.candidate store
  let distance := LatticeSquaredDistanceMachine.distanceStep refs.distance candidate.1
  (distance.1, (candidate.2, distance.2))

/-- Original offset loading, original candidate construction and actual initialized distance. -/
def candidateDistancePrefixInto (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width) :
    Circuit model ctx ctx :=
  .seq (LatticeOffsetMaterializer.setOffsetInto offset refs.materializer)
    (candidateDistanceInto refs)

/-- Complete actual stores and chronological native paths for all three original phases. -/
def prefixStep (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidateDistancePrefixInto offset refs).Path :=
  let materialized := LatticeOffsetMaterializer.setOffsetStep offset refs.materializer store
  let suffix := candidateDistanceStep refs materialized.1
  (suffix.1, (materialized.2, suffix.2))

/-- Actual candidate and distance composition retains all incoming histories and state blocks. -/
theorem candidateDistanceInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidateDistanceInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := candidateDistanceStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [candidateDistanceInto, Circuit.execute_seq,
    LatticeShortLogCandidatePoint.candidatePointInto_execute,
    LatticeSquaredDistanceMachine.squaredDistanceInto_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual three-phase prefix preserves every original reference correlation and history. -/
theorem candidateDistancePrefixInto_execute (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidateDistancePrefixInto offset refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := prefixStep offset refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [candidateDistancePrefixInto, Circuit.execute_seq,
    LatticeOffsetMaterializer.setOffsetInto_execute, candidateDistanceInto_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every actual caller read outside the three original phase footprints is retained. -/
theorem candidateDistancePrefixInto_callerFrame (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (prefixStep offset refs store).1 := by
  intro shape other materializer candidate distance
  change (LatticeSquaredDistanceMachine.distanceStep refs.distance
    (LatticeShortLogCandidatePoint.candidateStep refs.candidate
      (LatticeOffsetMaterializer.setOffsetStep offset refs.materializer store).1).1).1.read
        other = _
  rw [LatticeSquaredDistanceMachine.squaredDistanceInto_callerFrame refs.distance _ other
      distance.1 distance.2.1 distance.2.2.1 distance.2.2.2.1 distance.2.2.2.2,
    LatticeShortLogCandidatePoint.candidatePointInto_callerFrame refs.candidate _ other candidate,
    LatticeOffsetMaterializer.setOffsetInto_callerFrame offset refs.materializer store other
      materializer]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateDistancePrefix
