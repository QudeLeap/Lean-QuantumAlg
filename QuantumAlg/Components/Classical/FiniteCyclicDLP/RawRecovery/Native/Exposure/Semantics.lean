/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure
public import QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Copy
public import
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Values
public import QuantumAlg.Core.Algorithm.ClassicalOp
public import QuantumAlg.Core.Base.Model
public import QuantumAlg.Core.Base.Register
public import QuantumAlg.Core.Execution.Store
public import QuantumAlg.Core.Execution.State
public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Util.Classical.Modular.Basic
public import Mathlib.Data.Fintype.Defs
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Checked
import all
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Placement.Semantics
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

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

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual single recovery exposes the original three cells and retains the caller frame. -/
public theorem singleIntoCells_actualRecord (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (singleIntoCells (model := model) spec input inverseSuccess candidate reconstruction).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (singleIntoCells (model := model) spec input inverseSuccess candidate
          reconstruction).execute Reference state =
          @ExecutionState.mapClassical _ _ _ _ _ (Classical.decEq _) state (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (record before).1.1 =
        exposureWrite inverseSuccess candidate reconstruction before.1
          (RawRecovery.outputCells spec (preparationInput (before.1.read input))) := by
  unfold singleIntoCells
  obtain ⟨record, equation, correct⟩ :=
    withPreparation_actualRecord_post (model := model) spec input
      (fun refs transport => withCheckedExposure (model := model) spec refs
        (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
        (transport.liftWrite reconstruction))
      (fun before after => after = exposureWrite inverseSuccess candidate reconstruction before
        (RawRecovery.outputCells spec (preparationInput (before.read input)))) (by
        intro inner cells _distinct transport _separated
        obtain ⟨innerRecord, innerEquation, innerCorrect⟩ :=
          withCheckedExposure_actualRecord (model := model) spec (preparationRefs cells)
            (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
            (transport.liftWrite reconstruction)
        refine ⟨innerRecord, innerEquation, ?_⟩
        intro source prepared reads modulusValue leftValue rightValue
        have exactOutput := (innerCorrect prepared).2
          (preparationInput (source.read input)) modulusValue leftValue rightValue
        refine ⟨exposureWrite inverseSuccess candidate reconstruction source
          (RawRecovery.outputCells spec (preparationInput (source.read input))), rfl, ?_⟩
        rw [exactOutput]
        intro shape other
        exact exposureWrite_readsAs transport inverseSuccess candidate reconstruction source
          prepared.1 reads
          (RawRecovery.outputCells spec (preparationInput (source.read input))) other)
  refine ⟨record, ?_, correct⟩
  intro Reference History _ state
  rw [equation Reference state]
  apply ExecutionState.executionState_mapClassical_congr_decision
  intro entry
  rfl

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
