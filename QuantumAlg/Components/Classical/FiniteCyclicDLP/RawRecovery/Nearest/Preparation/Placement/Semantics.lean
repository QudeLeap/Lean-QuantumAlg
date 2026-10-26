/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Preparation.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Placement
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Record

/-!
# Actual fourteen-cell nearest preparation and its normalized continuation

The real lexical allocator supplies all separation and initializer facts.
The actual prepared store, complete coherent Reference and full earlier
History then enter the checked consumer with exact nearest-normalized values.
Every actual allocation, instruction and release remains in the same record.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular RawRecovery.Native

noncomputable section

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Fourteen fresh cells give native separation and protect the additional rounding-half cell. -/
lemma preparationRefs_nearest_separation (cells : Cells ctx (preparationShapes width))
    (distinct : cells.Distinct) :
    PreparationSeparation (preparationRefs cells.tail) cells.head.ref := by
  cases cells with
  | cons half tail =>
      refine ⟨preparationRefs_separated tail distinct.2, ?_⟩
      intro index same
      have free := Cells.workspaceCells_avoidsKey_not_mem_keys tail half.ref.key distinct.1
      apply free
      change half.ref.key = (preparationRefs tail).key index at same
      rw [same, preparationRefs_key]
      exact workspaceCells_cellAt_key_mem_keys tail index.rev

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}

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
        (Store inner × model.HiddenState) × (consumer (preparationRefs cells.tail) transport).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference (model.HiddenState × History)),
          (consumer (preparationRefs cells.tail) transport).execute environment Reference state =
            state.mapClassical (fun entry =>
              let result := step (entry.1, entry.2.1)
              (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
        ∀ (source : Store ctx) (prepared : Store inner × model.HiddenState),
          transport.ReadsAs source prepared.1 →
          (prepared.1.read (scaleRead (preparationRefs cells.tail).modulusWide)).toNat =
            spec.modulus →
          (prepared.1.read (scaleRead (preparationRefs cells.tail).left)).toNat =
            (normalizeInput spec (preparationInput (source.read input))).left.val →
          (prepared.1.read (scaleRead (preparationRefs cells.tail).negatedRight)).toNat =
            (negateRight spec (normalizeInput spec (preparationInput (source.read input)))).val →
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
  have separatedTail : cells.tail.TransportSeparated transport := by
    cases cells with
    | cons _ _ => exact separated.2
  have separatedHalf : ∀ {shape : CShape} (other : CInputRef ctx shape),
      cells.head.ref.key ∉ (transport.liftInput other).storageKeys := by
    cases cells with
    | cons _ _ => exact separated.1
  obtain ⟨step, equation, correct⟩ := consumerContract cells distinct transport separated
  refine ⟨Circuit.sequenceRecord _ _
    (fun before =>
      let result := preparationStep (model := model) spec (transport.liftInput input)
        (preparationRefs cells.tail) cells.head.ref before.1
      ((result.1, before.2), result.2)) step,
    Circuit.execute_sequenceRecord (environment := environment) _ _ _ _
      (fun reference {_} _ initial =>
        (preparationBody_execute (model := model) spec (transport.liftInput input)
          (preparationRefs cells.tail) cells.head.ref reference initial).trans
            (ExecutionState.executionState_mapClassical_congr _ rfl))
      equation, ?_⟩
  intro source before reads initialized
  let prepared :=
    (preparationStep (model := model) spec (transport.liftInput input) (preparationRefs cells.tail)
      cells.head.ref before.1).1
  have preparedReads : transport.ReadsAs source prepared := by
    intro shape other
    exact (preparationBody_read_other (model := model) spec (transport.liftInput input)
      (preparationRefs cells.tail) cells.head.ref (transport.liftInput other)
      (fun index => preparationRefs_transport_avoids cells.tail transport separatedTail index other)
      (separatedHalf other) before.1).trans (reads other)
  have initializedTail : cells.tail.Initialized before.1 := by
    cases cells with
    | cons _ _ => exact initialized.2
  obtain ⟨denominatorZero, zeroValue⟩ :=
    preparationRefs_initialized_zero cells.tail before.1 initializedTail
  have values := preparationBody_original_values (model := model) spec (transport.liftInput input)
    (preparationRefs cells.tail) cells.head.ref
    (preparationRefs_nearest_separation cells distinct) before.1
    denominatorZero zeroValue
  dsimp only at values
  rw [reads input] at values
  exact correct source (prepared, before.2) preparedReads values.1 values.2.1 values.2.2

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
