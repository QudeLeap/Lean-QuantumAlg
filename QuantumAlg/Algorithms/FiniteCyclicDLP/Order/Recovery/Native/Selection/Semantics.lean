/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Semantics
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection
public import QuantumAlg.Components.Classical.FirstAccepted.Semantics
public import QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted

/-!
# Full-state semantics of checked candidate selection

Each retained sample executes the complete raw recovery and abstract group
verification before the existing first-accepted selector runs.  The records
retain persistent oracle state, arbitrary quantum references and prior history.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G]
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- The actual attempt and first-accepted update have one chronological record. -/
public theorem selectAttempt_actualRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P)) :
    ∃ record : Store ctx × (OrderExecution.model P).HiddenState →
        (Store ctx × (OrderExecution.model P).HiddenState) ×
          (selectAttempt P spec input refs).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)),
        (selectAttempt P spec input refs).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  obtain ⟨record, equation⟩ := withAttempt_actualRecord P spec input (fun
      {inner} candidate accepted transport =>
        FirstAccepted.circuit (model := OrderExecution.model P)
          ⟨accepted, candidate⟩ (liftSelector refs transport)) (by
    intro inner candidate accepted transport
    let inputs : FirstAccepted.Inputs inner (OrderPreparation.width P) :=
      ⟨accepted, candidate⟩
    let lifted := liftSelector refs transport
    refine ⟨(fun entry =>
        let result := FirstAccepted.step
          (model := OrderExecution.model P) inputs lifted entry.1
        ((result.1, entry.2), result.2)), ?_⟩
    intro Reference History _ state
    exact (FirstAccepted.firstAccepted_execute
      (model := OrderExecution.model P) inputs lifted Reference state).trans
        (mapClassicalExplicit_eq state _).symm)
  refine ⟨record, ?_⟩
  intro Reference History _ state
  exact (equation Reference state).trans (mapClassicalExplicit_eq state _)

/-- Choose the witnessed store, service-state and path map of one attempt. -/
public def selectionAttemptRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P)) :
    Store ctx × (OrderExecution.model P).HiddenState →
      (Store ctx × (OrderExecution.model P).HiddenState) ×
        (selectAttempt P spec input refs).Path :=
  Classical.choose (selectAttempt_actualRecord P spec input refs)

/-- The chosen attempt record is witnessed by the full interpreter equation. -/
public theorem selectionAttemptRecord_execute
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (selectAttempt P spec input refs).execute Reference state =
      state.mapClassical (fun entry =>
        let result := selectionAttemptRecord P spec input refs (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Classical.choose_spec (selectAttempt_actualRecord P spec input refs) Reference state

/-- Complete record of all retained attempts in chronological order. -/
public def selectionLoopRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P)) :
    Store ctx × (OrderExecution.model P).HiddenState →
      (Store ctx × (OrderExecution.model P).HiddenState) ×
        (selectionLoop P spec count samples refs).Path :=
  Circuit.forRangeRecord (model := OrderExecution.model P) count
    (fun index => selectAttempt P spec (samples index) refs)
    (fun index => selectionAttemptRecord P spec (samples index) refs)

/-- Every retained attempt preserves arbitrary reference blocks and prior history. -/
public theorem selectionLoop_execute
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (selectionLoop P spec count samples refs).execute Reference state =
      state.mapClassical (fun entry =>
        let result := selectionLoopRecord P spec count samples refs (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord (model := OrderExecution.model P) count _ _
    (fun index => selectionAttemptRecord_execute P spec (samples index) refs)
    Reference state

private def packRecord {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (BitWord.instruction (execution := OrderExecution.model P)
        (selectionPack refs output)).Path :=
  let result := BitWord.instructionStep (execution := OrderExecution.model P)
    (selectionPack refs output) entry.1
  ((result.1, entry.2), result.2)

private theorem pack_execute {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (BitWord.instruction (execution := OrderExecution.model P)
      (selectionPack refs output)).execute Reference state =
      state.mapClassical (fun entry =>
        let result := packRecord P refs output (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  exact BitWord.bitWord_instruction_execute
    (execution := OrderExecution.model P) (selectionPack refs output) state

/-- The loop and final optional pack have one complete actual record. -/
public def recoveryBodyRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (output : CWriteRef ctx
      (.option (.unsignedWord (OrderPreparation.width P)))) :
    Store ctx × (OrderExecution.model P).HiddenState →
      (Store ctx × (OrderExecution.model P).HiddenState) ×
        (recoveryBody P spec count samples refs output).Path :=
  Circuit.sequenceRecord (model := OrderExecution.model P) _ _
    (selectionLoopRecord P spec count samples refs)
    (packRecord P refs output)

/-- The complete recovery body preserves the entire execution state shape. -/
public theorem recoveryBody_execute
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (output : CWriteRef ctx
      (.option (.unsignedWord (OrderPreparation.width P))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (recoveryBody P spec count samples refs output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := recoveryBodyRecord P spec count samples refs output
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_sequenceRecord (model := OrderExecution.model P) _ _ _ _
    (selectionLoop_execute P spec count samples refs) (pack_execute P refs output)
    Reference state

/-- Actual selector allocation surrounds the same complete loop and pack record. -/
public theorem recoveryInto_actualRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (output : CWriteRef ctx
      (.option (.unsignedWord (OrderPreparation.width P)))) :
    ∃ record : Store ctx × (OrderExecution.model P).HiddenState →
        (Store ctx × (OrderExecution.model P).HiddenState) ×
          (recoveryInto P spec count samples output).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)),
        (recoveryInto P spec count samples output).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  obtain ⟨record, equation, _⟩ :=
    withCells_actualRecord_initialized_restricted_post
      (model := OrderExecution.model P) ctx
      (selectorShapes (OrderPreparation.width P))
      (fun cells _ transport _ =>
        recoveryBody P spec count
          (fun index => transport.liftInput (samples index))
          (selectorRefs cells) (transport.liftWrite output))
      (fun _ _ => True) (by
        intro inner cells _distinct transport _separated
        exact ⟨recoveryBodyRecord P spec count
            (fun index => transport.liftInput (samples index))
            (selectorRefs cells) (transport.liftWrite output),
          recoveryBody_execute P spec count
            (fun index => transport.liftInput (samples index))
            (selectorRefs cells) (transport.liftWrite output),
          by intros; trivial⟩)
  exact ⟨record, equation⟩

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
