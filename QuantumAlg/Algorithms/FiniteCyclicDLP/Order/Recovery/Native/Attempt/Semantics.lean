/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Power.Semantics
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt
public import QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Semantics
public import QuantumAlg.Core.Execution.Classical.Workspace.Transport
public import QuantumAlg.Util.Classical.Modular.Basic
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Power.Semantics

/-!
# Full-state record of one checked recovery attempt

Raw integer recovery, the explicitly reset hidden group-power service and both
acceptance conjunctions share one chronological record. The record retains the
persistent oracle state, arbitrary quantum references and prior history.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]
variable (P : KnownOrderProblem G) {ctx : RuntimeCtx .quantum}

/-- Map the classical result while selecting its finite equality instance explicitly. -/
@[expose] public noncomputable def mapClassicalExplicit {C D : Type}
    [Fintype C] [Fintype D] {Reference : Register}
    (state : ExecutionState C Reference) (f : C → D) :
    ExecutionState D Reference :=
  @ExecutionState.mapClassical C D _ _ Reference (Classical.decEq D) state f

public theorem mapClassicalExplicit_eq {C D : Type}
    [Fintype C] [Fintype D] [DecidableEq D] {Reference : Register}
    (state : ExecutionState C Reference) (f : C → D) :
    mapClassicalExplicit state f = state.mapClassical f := by
  unfold mapClassicalExplicit
  cases Subsingleton.elim (Classical.decEq D) (inferInstance : DecidableEq D)
  rfl

/-- Compose two chronological records while fixing the finite equality instance
used by the classical-state map. -/
public theorem execute_sequenceRecord_explicit
    {model : ExecutionModel} {inner : RuntimeCtx model.kind}
    (first second : Circuit model inner inner)
    (firstStep : Store inner × model.HiddenState →
      (Store inner × model.HiddenState) × first.Path)
    (secondStep : Store inner × model.HiddenState →
      (Store inner × model.HiddenState) × second.Path)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State inner Reference (model.HiddenState × History)),
      first.execute Reference state = mapClassicalExplicit state (fun entry =>
        let result := firstStep (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State inner Reference (model.HiddenState × History)),
      second.execute Reference state = mapClassicalExplicit state (fun entry =>
        let result := secondStep (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State inner Reference (model.HiddenState × History)) :
    (Circuit.seq first second).execute Reference state =
      mapClassicalExplicit state (fun entry =>
        let result := Circuit.sequenceRecord first second firstStep secondStep
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  classical
  rw [mapClassicalExplicit_eq]
  apply Circuit.execute_sequenceRecord first second firstStep secondStep
  · intro reference history _ input
    exact (firstEquation reference input).trans
      (mapClassicalExplicit_eq input _)
  · intro reference history _ input
    exact (secondEquation reference input).trans
      (mapClassicalExplicit_eq input _)

private def literalRecord {input output : CShape}
    (op : ClassicalOp input output ctx ctx)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (BitWord.instruction (execution := OrderExecution.model P) op).Path :=
  let selected := BitWord.instructionStep (execution := OrderExecution.model P) op entry.1
  ((selected.1, entry.2), selected.2)

private theorem literal_execute {input output : CShape}
    (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (BitWord.instruction (execution := OrderExecution.model P) op).execute Reference state =
      mapClassicalExplicit state (fun entry =>
        let selected := literalRecord P op (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  classical
  rw [mapClassicalExplicit_eq]
  exact BitWord.bitWord_instruction_execute (execution := OrderExecution.model P) op state

/-- Full chronological record of both native conjunctions. -/
public def acceptanceRecord {width : Nat} (refs : AttemptRefs ctx width)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (acceptanceSuffix P refs).Path :=
  Circuit.sequenceRecord
    (BitWord.instruction (execution := OrderExecution.model P) (rawAcceptanceOp refs))
    (BitWord.instruction (execution := OrderExecution.model P) (candidateAcceptanceOp refs))
    (literalRecord P (rawAcceptanceOp refs))
    (literalRecord P (candidateAcceptanceOp refs)) entry

/-- The visible store update is exactly the two conjunctions. -/
public theorem acceptanceRecord_store {width : Nat} (refs : AttemptRefs ctx width)
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (acceptanceRecord P refs entry).1.1 =
      (entry.1.applyOp (rawAcceptanceOp refs)).applyOp (candidateAcceptanceOp refs) := by
  rfl

public theorem acceptanceSuffix_execute {width : Nat} (refs : AttemptRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (acceptanceSuffix P refs).execute Reference state =
      mapClassicalExplicit state (fun entry =>
        let selected := acceptanceRecord P refs (entry.1, entry.2.1)
        (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  exact execute_sequenceRecord_explicit
    (BitWord.instruction (execution := OrderExecution.model P) (rawAcceptanceOp refs))
    (BitWord.instruction (execution := OrderExecution.model P) (candidateAcceptanceOp refs))
    (literalRecord P (rawAcceptanceOp refs))
    (literalRecord P (candidateAcceptanceOp refs))
    (literal_execute P (rawAcceptanceOp refs))
    (literal_execute P (candidateAcceptanceOp refs)) Reference state

/-- Raw recovery, group verification and a proved continuation have one actual record. -/
public theorem attemptBody_actualRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : AttemptRefs ctx (OrderPreparation.width P))
    (body : CInputRef ctx (.unsignedWord (OrderPreparation.width P)) →
      CInputRef ctx .bit → Circuit (OrderExecution.model P) ctx ctx)
    (bodyContract :
      ∃ step : Store ctx × (OrderExecution.model P).HiddenState →
          (Store ctx × (OrderExecution.model P).HiddenState) ×
            (body (.storage refs.candidate.toCStorageRef)
              (.storage refs.acceptedCandidate.toCStorageRef)).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)),
          (body (.storage refs.candidate.toCStorageRef)
              (.storage refs.acceptedCandidate.toCStorageRef)).execute Reference state =
            mapClassicalExplicit state (fun entry =>
              let selected := step (entry.1, entry.2.1)
              (selected.1.1, (selected.1.2, (entry.2.2, selected.2))))) :
    ∃ step : Store ctx × (OrderExecution.model P).HiddenState →
        (Store ctx × (OrderExecution.model P).HiddenState) ×
          (attemptBody P spec input refs body).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)),
        (attemptBody P spec input refs body).execute Reference state =
          mapClassicalExplicit state (fun entry =>
            let selected := step (entry.1, entry.2.1)
            (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  classical
  obtain ⟨rawStep, rawEquation, _rawValues⟩ :=
    RawRecovery.Native.singleIntoCells_actualRecord
      (model := OrderExecution.model P) spec input refs.inverseSuccess
      refs.candidate refs.reconstruction
  obtain ⟨bodyStep, bodyEquation⟩ := bodyContract
  let candidate : CInputRef ctx (.unsignedWord (OrderPreparation.width P)) :=
    .storage refs.candidate.toCStorageRef
  let continued := body candidate (.storage refs.acceptedCandidate.toCStorageRef)
  let tailStep := Circuit.sequenceRecord
    (powerCheck P candidate refs.powerEqualsTarget)
    (.seq (acceptanceSuffix P refs) continued)
    (powerCheckRecord P candidate refs.powerEqualsTarget)
    (Circuit.sequenceRecord (acceptanceSuffix P refs) continued
      (acceptanceRecord P refs) bodyStep)
  have rawEquationExplicit : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)),
      (RawRecovery.Native.singleIntoCells (model := OrderExecution.model P)
          spec input refs.inverseSuccess refs.candidate refs.reconstruction).execute
            Reference state =
        mapClassicalExplicit state (fun entry =>
          let result := rawStep (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
    intro Reference History _ state
    simpa only [mapClassicalExplicit] using rawEquation Reference state
  have powerEquationExplicit : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)),
      (powerCheck P candidate refs.powerEqualsTarget).execute Reference state =
        mapClassicalExplicit state (fun entry =>
          let result := powerCheckRecord P candidate refs.powerEqualsTarget
            (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
    intro Reference History _ state
    exact (powerCheck_execute P candidate refs.powerEqualsTarget Reference state).trans
      (mapClassicalExplicit_eq state _).symm
  exact ⟨Circuit.sequenceRecord (model := OrderExecution.model P) _ _ rawStep tailStep,
    execute_sequenceRecord_explicit (model := OrderExecution.model P) _ _ _ _
      rawEquationExplicit
      (execute_sequenceRecord_explicit (model := OrderExecution.model P) _ _ _ _
        powerEquationExplicit
        (execute_sequenceRecord_explicit (model := OrderExecution.model P) _ _ _ _
          (acceptanceSuffix_execute P refs) bodyEquation))⟩

/-- Actual six-cell allocation and release surround the same complete attempt record. -/
public theorem withAttempt_actualRecord
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (body : ∀ {inner : RuntimeCtx .quantum},
      CInputRef inner (.unsignedWord (OrderPreparation.width P)) →
      CInputRef inner .bit → Transport ctx inner →
        Circuit (OrderExecution.model P) inner inner)
    (bodyContract : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord (OrderPreparation.width P)))
      (accepted : CInputRef inner .bit) (transport : Transport ctx inner),
      ∃ step : Store inner × (OrderExecution.model P).HiddenState →
          (Store inner × (OrderExecution.model P).HiddenState) ×
            (body candidate accepted transport).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference ((OrderExecution.model P).HiddenState × History)),
          (body candidate accepted transport).execute Reference state =
            mapClassicalExplicit state (fun entry =>
              let selected := step (entry.1, entry.2.1)
              (selected.1.1, (selected.1.2, (entry.2.2, selected.2))))) :
    ∃ step : Store ctx × (OrderExecution.model P).HiddenState →
        (Store ctx × (OrderExecution.model P).HiddenState) ×
          (withAttempt P spec input body).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)),
        (withAttempt P spec input body).execute Reference state =
          mapClassicalExplicit state (fun entry =>
            let selected := step (entry.1, entry.2.1)
            (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
  classical
  obtain ⟨step, equation, _⟩ :=
    withCells_actualRecord_initialized_restricted_post
      (model := OrderExecution.model P) ctx
      (attemptShapes (OrderPreparation.width P))
      (fun cells _ transport _ =>
        attemptBody P spec (transport.liftInput input) (attemptRefs cells)
          (fun candidate accepted => body candidate accepted transport))
      (fun _ _ => True) (by
        intro inner cells _distinct transport _separated
        obtain ⟨bodyStep, bodyEquation⟩ := bodyContract
          (.storage (attemptRefs cells).candidate.toCStorageRef)
          (.storage (attemptRefs cells).acceptedCandidate.toCStorageRef) transport
        let selectedBody := fun candidate accepted => body candidate accepted transport
        obtain ⟨attemptStep, attemptEquation⟩ :=
          attemptBody_actualRecord P spec (transport.liftInput input) (attemptRefs cells)
            selectedBody
            ⟨bodyStep, bodyEquation⟩
        have attemptEquationStandard :
            ∀ (Reference : Register) {History : Type} [Fintype History]
              (state : State inner Reference
                ((OrderExecution.model P).HiddenState × History)),
              (attemptBody P spec (transport.liftInput input) (attemptRefs cells)
                  selectedBody).execute Reference state =
                state.mapClassical (fun entry =>
                  let selected := attemptStep (entry.1, entry.2.1)
                  (selected.1.1, (selected.1.2, (entry.2.2, selected.2)))) := by
          intro Reference History _ state
          exact (attemptEquation Reference state).trans
            (mapClassicalExplicit_eq state _)
        exact ⟨attemptStep, attemptEquationStandard, by intros; trivial⟩)
  refine ⟨step, ?_⟩
  intro Reference History _ state
  exact (equation Reference state).trans (mapClassicalExplicit_eq state _).symm

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
