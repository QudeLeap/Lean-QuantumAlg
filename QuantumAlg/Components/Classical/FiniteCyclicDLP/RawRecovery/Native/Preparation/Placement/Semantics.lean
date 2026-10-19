/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Execution
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Placement
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Record

/-!
# Actual allocated raw-recovery preparation and its continuation

The thirteen lexical allocations supply every preparation separation and
initial-value premise. The continuation runs on the actual prepared store,
with the original normalized values and unchanged caller reads. Its actual
record is composed with preparation and all allocation push/pop operations;
the same resulting record proves the complete quantum-reference equation and
the caller-store postcondition.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- An actual deterministic continuation gives a complete record through all thirteen cells. -/
lemma withPreparation_hasRecord (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (consumer : ∀ {inner : RuntimeCtx model.kind}, PreparationRefs inner width →
      Transport ctx inner → Circuit model inner inner)
    (consumerRecord : ∀ {inner : RuntimeCtx model.kind}
      (cells : Cells inner (preparationShapes width)) (_distinct : cells.Distinct)
      (transport : Transport ctx inner) (_separated : cells.TransportSeparated transport),
      ∃ step : Store inner × model.HiddenState →
        (Store inner × model.HiddenState) × (consumer (preparationRefs cells) transport).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference (model.HiddenState × History)),
          (consumer (preparationRefs cells) transport).execute environment Reference state =
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
        (preparationRefs cells) before.1
      ((result.1, before.2), result.2)) step,
    Circuit.execute_sequenceRecord (environment := environment) _ _ _ _
      (fun reference {_} _ initial =>
        (preparationBody_execute (model := model) spec (transport.liftInput input)
          (preparationRefs cells) reference initial).trans
            (ExecutionState.executionState_mapClassical_congr _ rfl))
      equation⟩

/-- Preparation establishes the continuation's original values without any caller initialization. -/
lemma withPreparation_actualRecord_post (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (consumer : ∀ {inner : RuntimeCtx model.kind}, PreparationRefs inner width →
      Transport ctx inner → Circuit model inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (consumerContract : ∀ {inner : RuntimeCtx model.kind}
      (cells : Cells inner (preparationShapes width)) (_distinct : cells.Distinct)
      (transport : Transport ctx inner) (_separated : cells.TransportSeparated transport),
      ∃ step : Store inner × model.HiddenState →
        (Store inner × model.HiddenState) × (consumer (preparationRefs cells) transport).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference (model.HiddenState × History)),
          (consumer (preparationRefs cells) transport).execute environment Reference state =
            state.mapClassical (fun entry =>
              let result := step (entry.1, entry.2.1)
              (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
        ∀ (source : Store ctx) (prepared : Store inner × model.HiddenState),
          transport.ReadsAs source prepared.1 →
          (prepared.1.read (scaleRead (preparationRefs cells).modulusWide)).toNat = spec.modulus →
          (prepared.1.read (scaleRead (preparationRefs cells).left)).toNat =
            (normalize spec (preparationInput (source.read input))).left.val →
          (prepared.1.read (scaleRead (preparationRefs cells).negatedRight)).toNat =
            (negateRight spec (normalize spec (preparationInput (source.read input)))).val →
          ∃ target : Store ctx, Post source target ∧ transport.ReadsAs target (step prepared).1.1) :
    ∃ step : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (withPreparation (model := model) spec input consumer).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withPreparation (model := model) spec input consumer).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := step (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, Post before.1 (step before).1.1 := by
  unfold withPreparation
  apply withCells_actualRecord_initialized_post (environment := environment)
  intro inner cells distinct transport separated
  obtain ⟨step, equation, correct⟩ := consumerContract cells distinct transport separated
  refine ⟨Circuit.sequenceRecord _ _
    (fun before =>
      let result := preparationStep (model := model) spec (transport.liftInput input)
        (preparationRefs cells) before.1
      ((result.1, before.2), result.2)) step,
    Circuit.execute_sequenceRecord (environment := environment) _ _ _ _
      (fun reference {_} _ initial =>
        (preparationBody_execute (model := model) spec (transport.liftInput input)
          (preparationRefs cells) reference initial).trans
            (ExecutionState.executionState_mapClassical_congr _ rfl))
      equation, ?_⟩
  intro source before reads initialized
  let prepared :=
    (preparationStep (model := model) spec (transport.liftInput input) (preparationRefs cells)
      before.1).1
  have preparedReads : transport.ReadsAs source prepared := by
    intro shape other
    exact (preparationBody_read_other (model := model) spec (transport.liftInput input)
      (preparationRefs cells) (transport.liftInput other)
      (fun index => preparationRefs_transport_avoids cells transport separated index other)
      before.1).trans (reads other)
  obtain ⟨denominatorZero, zeroValue⟩ := preparationRefs_initialized_zero cells before.1 initialized
  have values := preparationBody_original_values (model := model) spec (transport.liftInput input)
    (preparationRefs cells) (preparationRefs_separated cells distinct) before.1
    denominatorZero zeroValue
  dsimp only at values
  rw [reads input] at values
  exact correct source (prepared, before.2) preparedReads values.1 values.2.1 values.2.2

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
