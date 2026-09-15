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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- An actual deterministic continuation gives a complete record through all thirteen cells. -/
theorem withPreparation_hasRecord (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (consumer : ∀ {inner : RuntimeCtx kind}, PreparationRefs inner width →
      Transport ctx inner → Circuit inner inner)
    (consumerRecord : ∀ {inner : RuntimeCtx kind}
      (cells : Cells inner (preparationShapes width)) (_distinct : cells.Distinct)
      (transport : Transport ctx inner) (_separated : cells.TransportSeparated transport),
      ∃ step : Store inner → Store inner × (consumer (preparationRefs cells) transport).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (consumer (preparationRefs cells) transport).execute Reference state =
            state.mapClassical (fun entry =>
              ((step entry.1).1, (entry.2, (step entry.1).2)))) :
    ∃ step : Store ctx → Store ctx × (withPreparation spec input consumer).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withPreparation spec input consumer).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2))) := by
  unfold withPreparation withCells
  apply withCellsFrom_hasRecord
  intro inner cells distinct transport separated
  obtain ⟨step, equation⟩ := consumerRecord cells distinct transport separated
  exact ⟨Circuit.sequenceRecord _ _
    (preparationStep spec (transport.liftInput input) (preparationRefs cells)) step,
    Circuit.execute_sequenceRecord _ _ _ _
      (preparationBody_execute spec (transport.liftInput input) (preparationRefs cells))
      equation⟩

/-- Preparation establishes the continuation's original values without any caller initialization. -/
theorem withPreparation_actualRecord_post (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (consumer : ∀ {inner : RuntimeCtx kind}, PreparationRefs inner width →
      Transport ctx inner → Circuit inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (consumerContract : ∀ {inner : RuntimeCtx kind}
      (cells : Cells inner (preparationShapes width)) (_distinct : cells.Distinct)
      (transport : Transport ctx inner) (_separated : cells.TransportSeparated transport),
      ∃ step : Store inner → Store inner × (consumer (preparationRefs cells) transport).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (consumer (preparationRefs cells) transport).execute Reference state =
            state.mapClassical (fun entry =>
              ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
        ∀ (source : Store ctx) (prepared : Store inner), transport.ReadsAs source prepared →
          (prepared.read (scaleRead (preparationRefs cells).modulusWide)).toNat = spec.modulus →
          (prepared.read (scaleRead (preparationRefs cells).left)).toNat =
            (normalize spec (preparationInput (source.read input))).left.val →
          (prepared.read (scaleRead (preparationRefs cells).negatedRight)).toNat =
            (negateRight spec (normalize spec (preparationInput (source.read input)))).val →
          ∃ target : Store ctx, Post source target ∧ transport.ReadsAs target (step prepared).1) :
    ∃ step : Store ctx → Store ctx × (withPreparation spec input consumer).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withPreparation spec input consumer).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  unfold withPreparation
  apply withCells_actualRecord_initialized_post
  intro inner cells distinct transport separated
  obtain ⟨step, equation, correct⟩ := consumerContract cells distinct transport separated
  refine ⟨Circuit.sequenceRecord _ _
    (preparationStep spec (transport.liftInput input) (preparationRefs cells)) step,
    Circuit.execute_sequenceRecord _ _ _ _
      (preparationBody_execute spec (transport.liftInput input) (preparationRefs cells))
      equation, ?_⟩
  intro source before reads initialized
  let prepared :=
    (preparationStep spec (transport.liftInput input) (preparationRefs cells) before).1
  have preparedReads : transport.ReadsAs source prepared := by
    intro shape other
    exact (preparationBody_read_other spec (transport.liftInput input)
      (preparationRefs cells) (transport.liftInput other)
      (fun index => preparationRefs_transport_avoids cells transport separated index other)
      before).trans (reads other)
  obtain ⟨denominatorZero, zeroValue⟩ := preparationRefs_initialized_zero cells before initialized
  have values := preparationBody_original_values spec (transport.liftInput input)
    (preparationRefs cells) (preparationRefs_separated cells distinct) before
    denominatorZero zeroValue
  dsimp only at values
  rw [reads input] at values
  exact correct source prepared preparedReads values.1 values.2.1 values.2.2

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
