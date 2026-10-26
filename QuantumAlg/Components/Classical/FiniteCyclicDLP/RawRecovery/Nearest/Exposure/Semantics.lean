/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Exposure.Checked
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Preparation.Placement.Semantics
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Complete actual nearest recovery and three-cell exposure

Actual measured decoding, paid nearest rounding, canonical modular wrap,
signed-right normalization and checked inversion feed the original native
candidate multiplication and reconstruction.  The actual complete record
returns exactly three caller writes and releases all lexical cells, retaining
every earlier History and quantum Reference matrix block.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular RawRecovery.Native

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual single recovery exposes the original three cells and retains the caller frame. -/
lemma singleIntoCells_actualRecord (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (singleIntoCells (model := model) spec input inverseSuccess candidate reconstruction).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (singleIntoCells (model := model) spec input inverseSuccess candidate
          reconstruction).execute environment Reference state =
          @ExecutionState.mapClassical _ _ _ _ _ (Classical.decEq _) state (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (record before).1.1 =
        exposureWrite inverseSuccess candidate reconstruction before.1
          (outputCellsInput spec (preparationInput (before.1.read input))) := by
  unfold singleIntoCells
  obtain ⟨record, equation, correct⟩ :=
    withPreparation_actualRecord_post (environment := environment) (model := model) spec input
      (fun refs transport => withCheckedExposure (model := model) spec refs
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction))
      (fun before after => after = exposureWrite inverseSuccess candidate reconstruction before
        (outputCellsInput spec (preparationInput (before.read input)))) (by
        intro inner cells _distinct transport _separated
        obtain ⟨innerRecord, innerEquation, innerCorrect⟩ :=
          withCheckedExposure_normalized_record (environment := environment)
            (model := model) spec (preparationRefs cells.tail)
            (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
            (transport.liftWrite reconstruction)
        refine ⟨innerRecord, innerEquation, ?_⟩
        intro source prepared reads modulusValue leftValue rightValue
        have exactOutput := (innerCorrect prepared).2
          (normalizeInput spec (preparationInput (source.read input)))
          modulusValue leftValue rightValue
        refine ⟨exposureWrite inverseSuccess candidate reconstruction source
          (outputCellsInput spec (preparationInput (source.read input))), rfl, ?_⟩
        rw [exactOutput]
        intro shape other
        exact exposureWrite_readsAs transport inverseSuccess candidate reconstruction source
          prepared.1 reads
          (outputCellsInput spec (preparationInput (source.read input))) other)
  refine ⟨record, ?_, correct⟩
  intro Reference History _ state
  rw [equation Reference state]
  apply ExecutionState.executionState_mapClassical_congr_decision
  intro entry
  rfl

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
