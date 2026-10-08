/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Selection.Frames

/-!
# Original three-check first-success selection from actual stored values
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private theorem bitAnd_value (left right : CShape.Value .bit) :
    (Resource.BitOpcode.eval .and (.product left right)).toBool =
      (left.toBool && right.toBool) := by
  cases left
  cases right
  rfl

/-- The original intermediate and complete candidate predicates after both actual conjunctions. -/
theorem candidateEligibilityInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    ((eligibilityStep refs store).1.read (writeInput refs.intermediate)).toBool =
        ((store.read refs.nearTarget).toBool && (store.read refs.exponentInRange).toBool) ∧
      ((eligibilityStep refs store).1.read (writeInput refs.eligible)).toBool =
        eligibility refs store := by
  let middle := store.applyOp (intermediateOp refs)
  have firstValue : (middle.read (writeInput refs.intermediate)).toBool =
      ((store.read refs.nearTarget).toBool && (store.read refs.exponentInRange).toBool) := by
    change ((store.applyOp (intermediateOp refs)).read
      (.storage (intermediateOp refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    exact bitAnd_value _ _
  constructor
  · change ((middle.applyOp (eligibleOp refs)).read (writeInput refs.intermediate)).toBool = _
    rw [Store.read_applyOp_of_not_mem_storageKeys middle (eligibleOp refs)
      (writeInput refs.intermediate)
      (mutable_avoids refs separation refs.intermediate .intermediate .eligible rfl (by decide))]
    exact firstValue
  · change ((middle.applyOp (eligibleOp refs)).read
      (.storage (eligibleOp refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    change (Resource.BitOpcode.eval .and (.product (middle.read (writeInput refs.intermediate))
      (middle.read refs.powerMatches))).toBool = _
    rw [bitAnd_value, firstValue]
    have powerFrame := Store.read_applyOp_of_not_mem_storageKeys store (intermediateOp refs)
      refs.powerMatches (separation.powerMatchesAvoidsMutable .intermediate)
    change middle.read refs.powerMatches = store.read refs.powerMatches at powerFrame
    rw [powerFrame]
    rfl

/-- Exact original predicates, persistent first-success latches and full actual caller frame. -/
structure Outcome (refs : Refs ctx width) (before after : Store ctx) : Prop where
  intermediate : (after.read (writeInput refs.intermediate)).toBool =
    ((before.read refs.nearTarget).toBool && (before.read refs.exponentInRange).toBool)
  eligible : (after.read (writeInput refs.eligible)).toBool = eligibility refs before
  accepted : (after.read (writeInput refs.selection.accepted)).toBool =
    ((before.read (writeInput refs.selection.accepted)).toBool || eligibility refs before)
  selected : after.read (writeInput refs.selection.selected) =
    if (!(before.read (writeInput refs.selection.accepted)).toBool && eligibility refs before) then
      before.read refs.candidate else before.read (writeInput refs.selection.selected)
  callerFrame : CallerFrame refs before after

/-- Actual range, distance and modular tests retain exactly the first eligible candidate word. -/
theorem candidateSelectorInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) : Outcome refs store (selectorStep refs store).1 := by
  let middle := (eligibilityStep refs store).1
  have values := candidateEligibilityInto_correct refs separation store
  have selected := ClassicalRoutines.FirstAccepted.Direct.into_correct
    (writeInput refs.eligible) refs.candidate refs.selection (selection_separated refs separation)
    middle
  have acceptedFrame := candidateEligibilityInto_callerFrame refs store
    (writeInput refs.selection.accepted)
    (mutable_avoids refs separation refs.selection.accepted .accepted .intermediate rfl (by decide))
    (mutable_avoids refs separation refs.selection.accepted .accepted .eligible rfl (by decide))
  have selectedFrame := candidateEligibilityInto_callerFrame refs store
    (writeInput refs.selection.selected)
    (mutable_avoids refs separation refs.selection.selected .selected .intermediate rfl (by decide))
    (mutable_avoids refs separation refs.selection.selected .selected .eligible rfl (by decide))
  have candidateFrame := candidateEligibilityInto_callerFrame refs store refs.candidate
    (separation.candidateAvoidsMutable .intermediate) (separation.candidateAvoidsMutable .eligible)
  have intermediateFrame := ClassicalRoutines.FirstAccepted.Direct.into_callerFrame
    (writeInput refs.eligible) refs.candidate refs.selection middle (writeInput refs.intermediate)
    (mutable_avoids refs separation refs.intermediate .intermediate .accepted rfl (by decide))
    (mutable_avoids refs separation refs.intermediate .intermediate .selected rfl (by decide))
  have eligibleFrame := ClassicalRoutines.FirstAccepted.Direct.into_callerFrame
    (writeInput refs.eligible) refs.candidate refs.selection middle (writeInput refs.eligible)
    (mutable_avoids refs separation refs.eligible .eligible .accepted rfl (by decide))
    (mutable_avoids refs separation refs.eligible .eligible .selected rfl (by decide))
  refine ⟨(congrArg CShape.Value.toBool intermediateFrame).trans values.1,
    (congrArg CShape.Value.toBool eligibleFrame).trans values.2, ?_, ?_,
    candidateSelectorInto_callerFrame refs store⟩
  · refine selected.accepted.trans ?_
    change ((middle.read (writeInput refs.selection.accepted)).toBool ||
      (middle.read (writeInput refs.eligible)).toBool) = _
    rw [acceptedFrame, values.2]
  · refine selected.selected.trans ?_
    change (if (!(middle.read (writeInput refs.selection.accepted)).toBool &&
      (middle.read (writeInput refs.eligible)).toBool) then middle.read refs.candidate
      else middle.read (writeInput refs.selection.selected)) = _
    rw [acceptedFrame, selectedFrame, candidateFrame, values.2]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelector
