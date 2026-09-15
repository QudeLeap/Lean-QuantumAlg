/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Checked
import all
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Placement.Semantics

/-!
# Complete actual three-cell raw recovery

Actual measured input preparation supplies the modulus and normalized words.
Actual checked inversion and selected recovery then expose the original three
observations. Every lexical workspace is released. The complete caller store
is exactly three chronological writes of the original `outputCells` model,
including destination aliases; the same record preserves full reference and
history. No caller workspace, inverse, or secret is supplied to the program.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual single recovery exposes the original three cells and retains the caller frame. -/
theorem singleIntoCells_actualRecord (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) :
    ∃ record : Store ctx → Store ctx ×
        (singleIntoCells spec input inverseSuccess candidate reconstruction).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (singleIntoCells spec input inverseSuccess candidate reconstruction).execute
          Reference state = state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 =
        exposureWrite inverseSuccess candidate reconstruction before
          (RawRecovery.outputCells spec (preparationInput (before.read input))) := by
  unfold singleIntoCells
  apply withPreparation_actualRecord_post spec input
    (fun refs transport => withCheckedExposure spec refs (transport.liftWrite inverseSuccess)
      (transport.liftWrite candidate) (transport.liftWrite reconstruction))
    (fun before after => after = exposureWrite inverseSuccess candidate reconstruction before
      (RawRecovery.outputCells spec (preparationInput (before.read input))))
  intro inner cells _distinct transport _separated
  obtain ⟨record, equation, correct⟩ := withCheckedExposure_actualRecord spec
    (preparationRefs cells) (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
    (transport.liftWrite reconstruction)
  refine ⟨record, equation, ?_⟩
  intro source prepared reads modulusValue leftValue rightValue
  have exactOutput := (correct prepared).2 (preparationInput (source.read input))
    modulusValue leftValue rightValue
  refine ⟨exposureWrite inverseSuccess candidate reconstruction source
    (RawRecovery.outputCells spec (preparationInput (source.read input))), rfl, ?_⟩
  rw [exactOutput]
  intro shape other
  exact exposureWrite_readsAs transport inverseSuccess candidate reconstruction source prepared
    reads (RawRecovery.outputCells spec (preparationInput (source.read input))) other

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
