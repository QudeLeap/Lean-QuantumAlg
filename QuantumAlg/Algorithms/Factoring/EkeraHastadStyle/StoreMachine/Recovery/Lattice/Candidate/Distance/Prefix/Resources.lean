/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Distance.Prefix.Correctness

/-!
# Actual candidate-distance-prefix native resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateDistancePrefix

open Execution

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent offset formula, eighteen candidate instructions and eight distance steps. -/
def prefixTrace (width : Nat) (offset : NumberTheory.IntegerPoint3) : List (Resource.Event model) :=
  LatticeOffsetMaterializer.offsetTrace width offset ++
    (LatticeCandidatePointMachine.candidateTrace width ++
      LatticeSquaredDistanceMachine.distanceTrace width)

/-- The actual three-phase prefix emits the complete independent native formula. -/
lemma candidateDistancePrefixInto_events (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (path : (candidateDistancePrefixInto offset refs).Path) :
    (candidateDistancePrefixInto offset refs).eventTrace path = prefixTrace width offset :=
  congrArg₂ List.append
    (LatticeOffsetMaterializer.setOffsetInto_events offset refs.materializer path.1)
    (congrArg₂ List.append
      (LatticeCandidatePointMachine.candidatePointInto_events
        (LatticeShortLogCandidatePoint.candidateRefs refs.candidate) path.2.1)
      (LatticeSquaredDistanceMachine.squaredDistanceInto_events refs.distance path.2.2))

/-- Native multiplicities account for all actual offset, candidate and distance instructions. -/
lemma candidateDistancePrefixInto_resourcePool (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (path : (candidateDistancePrefixInto offset refs).Path) :
    (candidateDistancePrefixInto offset refs).resourcePool path =
      ResourcePool.ofList (prefixTrace width offset) :=
  congrArg ResourcePool.ofList (candidateDistancePrefixInto_events offset refs path)

/-- Independent complete native count includes all three phases of the original candidate prefix. -/
def operationCount (offset : NumberTheory.IntegerPoint3) : Nat :=
  LatticeOffsetMaterializer.operationCount offset + 26

/-- Actual event count equals the complete independent candidate-prefix budget. -/
lemma candidateDistancePrefixInto_eventCount (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (path : (candidateDistancePrefixInto offset refs).Path) :
    ((candidateDistancePrefixInto offset refs).eventTrace path).length = operationCount offset := by
  change List.length (_ ++ (_ ++ _)) = _
  simp only [List.length_append]
  rw [LatticeOffsetMaterializer.setOffsetInto_eventCount]
  change LatticeOffsetMaterializer.operationCount offset + (18 + 8) = _
  rfl

/-- Actual dependency depth includes both offset initialization and distance initialization. -/
lemma candidateDistancePrefixInto_depth (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (path : (candidateDistancePrefixInto offset refs).Path) :
    (candidateDistancePrefixInto offset refs).depth (fun _ => 1) path = operationCount offset := by
  change (LatticeOffsetMaterializer.setOffsetInto offset refs.materializer).depth
    (fun _ => 1) path.1 + (18 + 8) = _
  rw [LatticeOffsetMaterializer.setOffsetInto_depth]
  rfl

/-- Actual candidate and distance work jointly restore all borrowed-reference states. -/
lemma candidateDistanceInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (candidateDistanceInto refs).BorrowedRestored Reference state
      ((candidateDistanceInto refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (LatticeShortLogCandidatePoint.candidatePointInto_borrowedRestored refs.candidate
      Reference state)
    (LatticeSquaredDistanceMachine.squaredDistanceInto_borrowedRestored refs.distance Reference _)

/-- The complete actual prefix restores every borrowed resource jointly with external references. -/
lemma candidateDistancePrefixInto_borrowedRestored (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (candidateDistancePrefixInto offset refs).BorrowedRestored Reference state
      ((candidateDistancePrefixInto offset refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (LatticeOffsetMaterializer.setOffsetInto_borrowedRestored offset refs.materializer
      Reference state)
    (candidateDistanceInto_borrowedRestored refs Reference _)

/-- Every actual candidate and distance instruction retains the entire original supplied context. -/
lemma candidateDistanceInto_visited (refs : Refs ctx width)
    (path : (candidateDistanceInto refs).Path) :
    (candidateDistanceInto refs).visitedContexts path = List.replicate 26 ctx := rfl

/-- All three actual phases preserve the original live context, including their scratch roles. -/
lemma candidateDistancePrefixInto_visited (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (path : (candidateDistancePrefixInto offset refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (candidateDistancePrefixInto offset refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈
    (LatticeOffsetMaterializer.setOffsetInto offset refs.materializer).visitedContexts path.1 ++
      (candidateDistanceInto refs).visitedContexts path.2 at present
  rw [candidateDistanceInto_visited] at present
  exact (List.mem_append.mp present).elim
    (LatticeOffsetMaterializer.setOffsetInto_visited offset refs.materializer path.1 visited)
    (fun member => (List.mem_replicate.mp member).2)

/-- Resident accounting includes every original live quantum and classical resource. -/
lemma candidateDistancePrefixInto_resident_le (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (path : (candidateDistancePrefixInto offset refs).Path) :
    (candidateDistancePrefixInto offset refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [candidateDistancePrefixInto_visited offset refs path visited present]

/-- Auxiliary accounting includes the supplied roles through all three actual phases. -/
lemma candidateDistancePrefixInto_auxiliary_le (offset : NumberTheory.IntegerPoint3)
    (refs : Refs ctx width) (path : (candidateDistancePrefixInto offset refs).Path) :
    (candidateDistancePrefixInto offset refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [candidateDistancePrefixInto_visited offset refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateDistancePrefix
