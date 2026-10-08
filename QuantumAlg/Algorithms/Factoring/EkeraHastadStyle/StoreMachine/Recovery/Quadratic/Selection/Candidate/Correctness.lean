/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Selection.Candidate.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Check.Correctness
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation

/-!
# Exact first-success update from actual checked candidate storage
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateSelect

open Execution
open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

private theorem map_retainFirst {α β : Type} (convert : α → β)
    (previous current : Option α) :
    (FirstAccepted.retainFirst previous current).map convert =
      FirstAccepted.retainFirst (previous.map convert) (current.map convert) := by
  cases previous <;> rfl

/-- All caller reads outside the possible check and selector writes are preserved. -/
theorem into_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other :=
  (FirstAccepted.firstAccepted_read_other (selectionInputs refs) refs.selection other
    avoids.available avoids.take avoids.accepted avoids.selected _).trans
    (QuadraticCandidateCheck.into_callerFrame refs.check store other avoids.check)

/-- Keep an existing selection; otherwise select exactly the current proper divisor. -/
theorem into_correct (refs : Refs ctx shortWidth) (separation : Separation refs)
    (store : Store ctx)
    (initial : QuadraticCandidateCheck.TotalInitialConditions store refs.check) :
    Relation refs store (step refs store).1 := by
  let checked := (QuadraticCandidateCheck.step refs.check store).1
  have checkHolds := QuadraticCandidateCheck.into_correct refs.check separation.check store initial
  have acceptedAtCheck := QuadraticCandidateCheck.into_callerFrame refs.check store
    (FirstAccepted.cellRead refs.selection.accepted) separation.acceptedFrame
  have selectedAtCheck := QuadraticCandidateCheck.into_callerFrame refs.check store
    (FirstAccepted.cellRead refs.selection.selected) separation.selectedFrame
  have previousAtCheck : selectedOption refs.selection checked =
      selectedOption refs.selection store := by
    unfold selectedOption FirstAccepted.selectedOption
    rw [acceptedAtCheck, selectedAtCheck]
  have candidateAtCheck := QuadraticCandidateCheck.into_callerFrame refs.check store
    refs.check.positiveCheck.candidate
    ⟨separation.check.candidateAvoidsDecision, separation.check.candidateFrame⟩
  have checkedAtCheck :
      (FirstAccepted.candidateOption (selectionInputs refs) checked).map CShape.Value.toNat =
        candidateOption refs store := by
    unfold FirstAccepted.candidateOption selectionInputs candidateOption
    rw [checkHolds.eligible, candidateAtCheck]
    split <;> simp_all
  have optionStep := congrArg (Option.map CShape.Value.toNat)
    (FirstAccepted.firstAccepted_selectedOption (selectionInputs refs) refs.selection
      separation.selection checked)
  rw [map_retainFirst] at optionStep
  change selectedOption refs.selection
    (FirstAccepted.step (selectionInputs refs) refs.selection checked).1 =
      FirstAccepted.retainFirst (selectedOption refs.selection checked)
        ((FirstAccepted.candidateOption (selectionInputs refs) checked).map
          CShape.Value.toNat) at optionStep
  rw [previousAtCheck, checkedAtCheck] at optionStep
  exact ⟨optionStep, into_callerFrame refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateSelect
