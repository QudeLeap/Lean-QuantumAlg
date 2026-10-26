/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Preparation
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Execution
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Record

/-!
# Complete actual execution records of nearest preparation

The same decoded stores feed both nearest scalings and the final sign branch.
The full actual record includes both seven-instruction paths and all fourteen
lexical allocation and release operations, while retaining arbitrary quantum
Reference, persistent service and History correlations.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular RawRecovery.Native

noncomputable section

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Both nearest scalings retain their real chronological instruction records. -/
def preparationScaleStep (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1)))) (store : Store ctx) :
    Store ctx × (preparationScale (model := model) refs half).Path :=
  let first := scaleStep (model := model) (scaleRefs refs half false) store
  let second := scaleStep (model := model) (scaleRefs refs half true) first.1
  (second.1, (first.2, second.2))

/-- Complete nearest preparation uses actual decoder, constant, arithmetic and sign results. -/
def preparationStep (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1)))) (store : Store ctx) :
    Store ctx × (preparationBody (model := model) spec input refs half).Path :=
  let decoded := preparationDecodeStep (model := model) input refs store
  let seeded := preparationConstantsStep (model := model) spec refs decoded.1
  let scaled := preparationScaleStep (model := model) refs half seeded.1
  let final := preparationFinalizeStep (model := model) refs scaled.1
  (final.1, ((decoded.2, seeded.2), (scaled.2, final.2)))

/-- The two nearest scalings preserve the complete caller and coherent Reference record. -/
lemma preparationScale_execute (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (preparationScale (model := model) refs half).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := preparationScaleStep (model := model) refs half entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (RawRecovery.Native.execute_preservingServiceSequence _ _ _ _
    (scaleBody_execute (model := model) (scaleRefs refs half false))
    (scaleBody_execute (model := model) (scaleRefs refs half true)) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The complete actual nearest prefix preserves every quantum-reference matrix and History. -/
lemma preparationBody_execute (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (preparationBody (model := model) spec input refs half).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := preparationStep (model := model) spec input refs half entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (RawRecovery.Native.execute_preservingServiceSequence
    (preparationDecodeSeed (model := model) spec input refs)
    ((preparationScale (model := model) refs half).seq
      (preparationFinalize (model := model) refs))
    (fun before =>
      let decoded := preparationDecodeStep (model := model) input refs before
      let seeded := preparationConstantsStep (model := model) spec refs decoded.1
      (seeded.1, (decoded.2, seeded.2)))
    (fun before =>
      let scaled := preparationScaleStep (model := model) refs half before
      let final := preparationFinalizeStep (model := model) refs scaled.1
      (final.1, (scaled.2, final.2))) ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (RawRecovery.Native.execute_preservingServiceSequence
      (preparationDecode (model := model) input refs)
      (preparationConstants (model := model) spec refs)
      (preparationDecodeStep (model := model) input refs)
      (preparationConstantsStep (model := model) spec refs)
      (preparationDecode_execute (model := model) input refs)
      (preparationConstants_execute (model := model) spec refs) reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    exact (RawRecovery.Native.execute_preservingServiceSequence
      (preparationScale (model := model) refs half) (preparationFinalize (model := model) refs)
      (preparationScaleStep (model := model) refs half)
      (preparationFinalizeStep (model := model) refs)
      (preparationScale_execute (model := model) refs half)
      (preparationFinalize_execute (model := model) refs) reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every actual deterministic continuation has a complete nearest-preparation allocation record. -/
lemma withPreparation_hasRecord (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (consumer : ∀ {inner : RuntimeCtx model.kind}, PreparationRefs inner width →
      Transport ctx inner → Circuit model inner inner)
    (consumerRecord : ∀ {inner : RuntimeCtx model.kind}
      (cells : Cells inner (preparationShapes width)) (_distinct : cells.Distinct)
      (transport : Transport ctx inner) (_separated : cells.TransportSeparated transport),
      ∃ step : Store inner × model.HiddenState →
        (Store inner × model.HiddenState) × (consumer (preparationRefs cells.tail) transport).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference (model.HiddenState × History)),
          (consumer (preparationRefs cells.tail) transport).execute environment Reference state =
            state.mapClassical (fun entry =>
              let result := step (entry.1, entry.2.1)
              (result.1.1, (result.1.2, (entry.2.2, result.2))))) :
    ∃ step : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (withPreparation (model := model) spec input consumer).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withPreparation (model := model) spec input consumer).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := step (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  unfold withPreparation withCells
  apply withCellsFrom_hasRecord (environment := environment)
  intro inner cells distinct transport separated
  obtain ⟨step, equation⟩ := consumerRecord cells distinct transport separated
  exact ⟨Circuit.sequenceRecord _ _
    (fun before =>
      let result := preparationStep (model := model) spec (transport.liftInput input)
        (preparationRefs cells.tail) cells.head.ref before.1
      ((result.1, before.2), result.2)) step,
    Circuit.execute_sequenceRecord (environment := environment) _ _ _ _
      (fun reference {_} _ initial =>
        (preparationBody_execute (model := model) spec (transport.liftInput input)
          (preparationRefs cells.tail) cells.head.ref reference initial).trans
            (ExecutionState.executionState_mapClassical_congr _ rfl)) equation⟩

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
