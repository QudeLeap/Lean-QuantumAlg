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
variable {oracles : OracleModel}
variable {quantumEnvironment : oracles.Interpretation}
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- The actual attempt and first-accepted update have one chronological record. -/
public lemma selectAttempt_actualRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P)) :
    ∃ record : Store ctx × (recoveryModel P oracles).HiddenState →
        (Store ctx × (recoveryModel P oracles).HiddenState) ×
          (selectAttempt (oracles := oracles) P spec input refs).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)),
        (selectAttempt (oracles := oracles) P spec input refs).execute
          (recoveryEnvironment P quantumEnvironment) Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  obtain ⟨record, equation⟩ := withAttempt_actualRecord (oracles := oracles) P spec input (fun
      {inner} candidate accepted transport =>
        FirstAccepted.circuit (model := recoveryModel P oracles)
          ⟨accepted, candidate⟩ (liftSelector refs transport)) (by
    intro inner candidate accepted transport
    let inputs : FirstAccepted.Inputs inner (OrderPreparation.width P) :=
      ⟨accepted, candidate⟩
    let lifted := liftSelector refs transport
    refine ⟨(fun entry =>
        let result := FirstAccepted.step
          (model := recoveryModel P oracles) inputs lifted entry.1
        ((result.1, entry.2), result.2)), ?_⟩
    intro Reference History _ state
    exact (FirstAccepted.firstAccepted_execute
      (environment := recoveryEnvironment P quantumEnvironment)
      (model := recoveryModel P oracles) inputs lifted Reference state).trans
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
    Store ctx × (recoveryModel P oracles).HiddenState →
      (Store ctx × (recoveryModel P oracles).HiddenState) ×
        (selectAttempt (oracles := oracles) P spec input refs).Path :=
  Classical.choose (selectAttempt_actualRecord
    (quantumEnvironment := quantumEnvironment) (oracles := oracles) P spec input refs)

/-- The chosen attempt record is witnessed by the full interpreter equation. -/
public lemma selectionAttemptRecord_execute
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (selectAttempt (oracles := oracles) P spec input refs).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let result := selectionAttemptRecord
          (quantumEnvironment := quantumEnvironment)
          (oracles := oracles) P spec input refs (entry.1,
          entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Classical.choose_spec (selectAttempt_actualRecord
    (quantumEnvironment := quantumEnvironment) (oracles := oracles) P spec input refs)
    Reference state

/-- Complete record of all retained attempts in chronological order. -/
public def selectionLoopRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P)) :
    Store ctx × (recoveryModel P oracles).HiddenState →
      (Store ctx × (recoveryModel P oracles).HiddenState) ×
        (selectionLoop (oracles := oracles) P spec count samples refs).Path :=
  Circuit.forRangeRecord (model := recoveryModel P oracles) count
    (fun index => selectAttempt (oracles := oracles) P spec (samples index) refs)
    (fun index => selectionAttemptRecord
      (quantumEnvironment := quantumEnvironment) (oracles := oracles) P spec (samples index) refs)

/-- Every retained attempt preserves arbitrary reference blocks and prior history. -/
public lemma selectionLoop_execute
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (selectionLoop (oracles := oracles) P spec count samples refs).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let result := selectionLoopRecord
          (quantumEnvironment := quantumEnvironment) (oracles := oracles) P spec count samples refs
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord (environment := recoveryEnvironment P quantumEnvironment)
    (model := recoveryModel P oracles) count _ _
    (fun index => selectionAttemptRecord_execute (oracles := oracles) P spec (samples index) refs)
    Reference state

private def packRecord {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (entry : Store ctx × (recoveryModel P oracles).HiddenState) :
    (Store ctx × (recoveryModel P oracles).HiddenState) ×
      (BitWord.instruction (execution := recoveryModel P oracles)
        (selectionPack refs output)).Path :=
  let result := BitWord.instructionStep (execution := recoveryModel P oracles)
    (selectionPack refs output) entry.1
  ((result.1, entry.2), result.2)

private lemma pack_execute {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (BitWord.instruction (execution := recoveryModel P oracles)
      (selectionPack refs output)).execute
        (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let result := packRecord (oracles := oracles) P refs output (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  exact BitWord.bitWord_instruction_execute
    (environment := recoveryEnvironment P quantumEnvironment)
    (execution := recoveryModel P oracles) (selectionPack refs output) state

/-- The loop and final optional pack have one complete actual record. -/
public def recoveryBodyRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (output : CWriteRef ctx
      (.option (.unsignedWord (OrderPreparation.width P)))) :
    Store ctx × (recoveryModel P oracles).HiddenState →
      (Store ctx × (recoveryModel P oracles).HiddenState) ×
        (recoveryBody (oracles := oracles) P spec count samples refs output).Path :=
  Circuit.sequenceRecord (model := recoveryModel P oracles) _ _
    (selectionLoopRecord
      (quantumEnvironment := quantumEnvironment) (oracles := oracles) P spec count samples refs)
    (packRecord (oracles := oracles) P refs output)

/-- The complete recovery body preserves the entire execution state shape. -/
public lemma recoveryBody_execute
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (output : CWriteRef ctx
      (.option (.unsignedWord (OrderPreparation.width P))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)) :
    (recoveryBody (oracles := oracles) P spec count samples refs output).execute
      (recoveryEnvironment P quantumEnvironment) Reference state =
      state.mapClassical (fun entry =>
        let result := recoveryBodyRecord
          (quantumEnvironment := quantumEnvironment)
          (oracles := oracles) P spec count samples refs output
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_sequenceRecord (environment := recoveryEnvironment P quantumEnvironment)
    (model := recoveryModel P oracles) _ _ _ _
    (selectionLoop_execute (oracles := oracles) P spec count samples refs) (pack_execute
      (oracles := oracles) P refs output)
    Reference state

/-- Actual selector allocation surrounds the same complete loop and pack record. -/
public lemma recoveryInto_actualRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (output : CWriteRef ctx
      (.option (.unsignedWord (OrderPreparation.width P)))) :
    ∃ record : Store ctx × (recoveryModel P oracles).HiddenState →
        (Store ctx × (recoveryModel P oracles).HiddenState) ×
          (recoveryInto (oracles := oracles) P spec count samples output).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)),
        (recoveryInto (oracles := oracles) P spec count samples output).execute
          (recoveryEnvironment P quantumEnvironment) Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  obtain ⟨record, equation, _⟩ :=
    withCells_actualRecord_initialized_restricted_post
      (environment := recoveryEnvironment P quantumEnvironment)
      (model := recoveryModel P oracles) ctx
      (selectorShapes (OrderPreparation.width P))
      (fun cells _ transport _ =>
        recoveryBody (oracles := oracles) P spec count
          (fun index => transport.liftInput (samples index))
          (selectorRefs cells) (transport.liftWrite output))
      (fun _ _ => True) (by
        intro inner cells _distinct transport _separated
        exact ⟨recoveryBodyRecord
          (quantumEnvironment := quantumEnvironment) (oracles := oracles) P spec count
            (fun index => transport.liftInput (samples index))
            (selectorRefs cells) (transport.liftWrite output),
          recoveryBody_execute (oracles := oracles) P spec count
            (fun index => transport.liftInput (samples index))
            (selectorRefs cells) (transport.liftWrite output),
          by intros; trivial⟩)
  exact ⟨record, equation⟩

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
