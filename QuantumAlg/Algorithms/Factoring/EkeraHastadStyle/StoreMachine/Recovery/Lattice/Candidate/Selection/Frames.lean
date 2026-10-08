/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Selection

/-!
# Actual candidate-selection separation and caller frames
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

omit [BitWord.Selected model] in
/-- Differently named original outputs have disjoint actual structural identities. -/
theorem mutable_avoids (refs : Refs ctx width) (separation : Separation refs)
    {shape : CShape} (source : CWriteRef ctx shape) (saved written : MutableCell)
    (sourceKey : source.key = mutableKey refs saved) (different : saved ≠ written) :
    mutableKey refs written ∉ (writeInput source).storageKeys := by
  change mutableKey refs written ∉ [source.key]
  simp only [List.mem_singleton]
  rw [sourceKey]
  intro equal
  exact different (separation.mutableKeyInjective equal.symm)

omit [BitWord.Selected model] in
/-- The original actual caller separation supplies the shared direct selector's full source
frame. -/
theorem selection_separated (refs : Refs ctx width) (separation : Separation refs) :
    ClassicalRoutines.FirstAccepted.Direct.Separation
      (writeInput refs.eligible) refs.candidate refs.selection := by
  refine ⟨mutable_avoids refs separation refs.eligible .eligible .accepted rfl (by decide),
    mutable_avoids refs separation refs.eligible .eligible .selected rfl (by decide),
    separation.candidateAvoidsMutable .accepted, separation.candidateAvoidsMutable .selected, ?_⟩
  intro equal
  have impossible : MutableCell.accepted = .selected := separation.mutableKeyInjective equal
  cases impossible

/-- The original two actual conjunctions preserve every other caller read. -/
theorem candidateEligibilityInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (intermediate : refs.intermediate.key ∉ other.storageKeys)
    (eligible : refs.eligible.key ∉ other.storageKeys) :
    (eligibilityStep refs store).1.read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys _ (eligibleOp refs) other eligible).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (intermediateOp refs) other intermediate)

/-- The actual suffix frame is the union of the original two conjunction and two persistent
writes. -/
theorem candidateSelectorInto_callerFrame (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (selectorStep refs store).1 := by
  intro shape other avoids
  exact (ClassicalRoutines.FirstAccepted.Direct.into_callerFrame
    (writeInput refs.eligible) refs.candidate refs.selection _ other
    (avoids .accepted) (avoids .selected)).trans
    (candidateEligibilityInto_callerFrame refs store other
      (avoids .intermediate) (avoids .eligible))

/-- The actual three original predicate inputs and candidate survive the complete selection
suffix. -/
theorem candidateSelectorInto_source_frame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (selectorStep refs store).1.read refs.nearTarget = store.read refs.nearTarget ∧
      (selectorStep refs store).1.read refs.exponentInRange = store.read refs.exponentInRange ∧
      (selectorStep refs store).1.read refs.powerMatches = store.read refs.powerMatches ∧
      (selectorStep refs store).1.read refs.candidate = store.read refs.candidate :=
  ⟨candidateSelectorInto_callerFrame refs store refs.nearTarget separation.nearTargetAvoidsMutable,
    candidateSelectorInto_callerFrame refs store refs.exponentInRange
      separation.exponentInRangeAvoidsMutable,
    candidateSelectorInto_callerFrame refs store refs.powerMatches
      separation.powerMatchesAvoidsMutable,
    candidateSelectorInto_callerFrame refs store refs.candidate separation.candidateAvoidsMutable⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector
