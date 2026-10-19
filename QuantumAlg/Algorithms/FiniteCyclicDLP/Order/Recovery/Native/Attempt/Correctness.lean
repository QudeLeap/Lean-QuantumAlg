/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Values
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Soundness
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Samples
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Probability
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Output
public import QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Samples
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Output
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Semantics
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Attempt.Values
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Values
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Copy
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store

/-!
# Correctness of one checked native-dimensional recovery attempt

A selected Fourier outcome drives the existing raw recovery to the advertised
secret.  The subsequent representation-independent group-power query accepts
that same candidate.  The secret remains proof-side evidence and is not an
input to the executable routine.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

noncomputable section

attribute [local instance] Classical.decEq

open Execution

universe u

variable {G : Type u} [Group G] [Fintype G]
variable {oracles : OracleModel}
variable {quantumEnvironment : oracles.Interpretation}

omit [Fintype G] in
private lemma preparation_rawSample (P : KnownOrderProblem G)
    (outcome : TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) :
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.preparationInput
        (OrderEndpoint.rawSample P outcome) = .bits outcome := by
  apply congrArg CShape.Value.bits
  funext index
  cases value : outcome index <;>
    simp only [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.measuredDecodeInput,
      OrderEndpoint.rawSample, CShape.Value.get, CShape.Value.toFin,
      value, Bool.false_eq_true, if_false, if_true]
  all_goals rfl

omit [Fintype G] in
/-- A selected source outcome writes the canonical bounded secret word. -/
public lemma attemptCandidateValue_selected (P : KnownOrderProblem G)
    (secret : Canonical.Probability.SecretInput P) (unit : (ZMod P.order)ˣ)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (modulus : spec.modulus = P.order) :
    attemptCandidateValue spec
        (OrderEndpoint.rawSample P
          (Canonical.Probability.selectedRawOutcome P secret unit)) =
      CShape.wordOfNat (OrderPreparation.width P) secret.secret.val := by
  obtain ⟨output, outputOf, candidate, verified⟩ :=
    FiniteCyclicDLP.Probability.RecoveryBridge.outputOf_selectedRawInput_recovers
      P secret unit spec modulus
  unfold attemptCandidateValue
  rw [preparation_rawSample]
  change
    (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells spec
      (Canonical.Probability.RecoveryBridge.selectedRawInput P secret unit)).second.first = _
  rw [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells_of_outputOf_some
    spec _ output outputOf]
  simp only [CShape.Value.second, CShape.Value.first]
  exact congrArg (CShape.wordOfNat (OrderPreparation.width P)) candidate

omit [Fintype G] in
/-- The raw flags and the declared group equation both accept a selected outcome. -/
public lemma attemptAcceptedValue_selected (P : KnownOrderProblem G)
    (secret : Canonical.Probability.SecretInput P) (unit : (ZMod P.order)ˣ)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (modulus : spec.modulus = P.order) :
    attemptAcceptedValue P spec
        (OrderEndpoint.rawSample P
          (Canonical.Probability.selectedRawOutcome P secret unit)) = true := by
  classical
  obtain ⟨output, outputOf, candidate, verified⟩ :=
    FiniteCyclicDLP.Probability.RecoveryBridge.outputOf_selectedRawInput_recovers
      P secret unit spec modulus
  unfold attemptAcceptedValue attemptCandidateValue
  rw [preparation_rawSample]
  change
    (let raw := ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells spec
      (Canonical.Probability.RecoveryBridge.selectedRawInput P secret unit)
    raw.first.toBool && raw.second.second.toBool &&
      decide (P.generator ^ raw.second.first.toNat = P.target)) = true
  rw [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells_of_outputOf_some
    spec _ output outputOf]
  simp only [CShape.Value.first, CShape.Value.second, CShape.Value.toBool,
    Bool.true_and, verified]
  rw [candidate]
  rw [secretWord_toNat P secret]
  rw [secret.target_eq_generator_pow]
  simp

private def attemptKeys {ctx : RuntimeCtx .quantum} {width : Nat}
    (refs : AttemptRefs ctx width) : List StorageKey :=
  [refs.acceptedCandidate.key, refs.rawAccepted.key, refs.powerEqualsTarget.key,
    refs.reconstruction.key, refs.candidate.key, refs.inverseSuccess.key]

private lemma attemptKeys_cells {ctx : RuntimeCtx .quantum} {width : Nat}
    (cells : ClassicalWorkspace.Cells ctx (attemptShapes width)) :
    attemptKeys (attemptRefs cells) = cells.keys := by
  cases cells with
  | cons accepted rest =>
      cases rest with
      | cons raw rest =>
          cases rest with
          | cons equality rest =>
              cases rest with
              | cons reconstruction rest =>
                  cases rest with
                  | cons candidate rest =>
                      cases rest with
                      | cons inverse rest => cases rest; rfl

private lemma raw_reads {ctx : RuntimeCtx .quantum} {width : Nat}
    (refs : AttemptRefs ctx width) (distinct : (attemptKeys refs).Nodup)
    (before : Execution.Store ctx)
    (raw : CShape.Value (.product .bit
      (ClassicalRoutines.FiniteCyclicDLP.OutputShape width))) :
    let after := ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.exposureWrite
      refs.inverseSuccess refs.candidate refs.reconstruction before raw
    after.read (.storage refs.inverseSuccess.toCStorageRef) = raw.first ∧
      after.read (.storage refs.candidate.toCStorageRef) = raw.second.first ∧
      after.read (.storage refs.reconstruction.toCStorageRef) = raw.second.second := by
  have candidateInverse : refs.candidate.key ≠ refs.inverseSuccess.key := by
    intro same
    simp [attemptKeys, same] at distinct
  have reconstructionInverse : refs.reconstruction.key ≠ refs.inverseSuccess.key := by
    intro same
    simp [attemptKeys, same] at distinct
  have reconstructionCandidate : refs.reconstruction.key ≠ refs.candidate.key := by
    intro same
    simp [attemptKeys, same] at distinct
  dsimp only
  unfold ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.exposureWrite
  refine ⟨?_, ?_, Execution.Store.read_write_same _ _ _⟩
  · rw [Execution.Store.read_write_other _ refs.reconstruction
      refs.inverseSuccess.toCStorageRef _ reconstructionInverse]
    rw [Execution.Store.read_write_other _ refs.candidate
      refs.inverseSuccess.toCStorageRef _ candidateInverse,
      Execution.Store.read_write_same]
  · rw [Execution.Store.read_write_other _ refs.reconstruction
      refs.candidate.toCStorageRef _ reconstructionCandidate,
      Execution.Store.read_write_same]

private lemma acceptanceRecord_preserves_read {ctx : RuntimeCtx .quantum} {width : Nat}
    (P : KnownOrderProblem G) (refs : AttemptRefs ctx width)
    (entry : Execution.Store ctx × (recoveryModel P oracles).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (rawFree : refs.rawAccepted.key ∉ other.storageKeys)
    (acceptedFree : refs.acceptedCandidate.key ∉ other.storageKeys) :
    (acceptanceRecord (oracles := oracles) P refs entry).1.1.read other = entry.1.read other := by
  rw [acceptanceRecord_store]
  exact (Execution.Store.read_applyOp_of_not_mem_storageKeys _
    (candidateAcceptanceOp refs) other acceptedFree).trans
      (Execution.Store.read_applyOp_of_not_mem_storageKeys _
        (rawAcceptanceOp refs) other rawFree)

private lemma verificationRecord_preserves_read {ctx : RuntimeCtx .quantum} {width : Nat}
    (P : KnownOrderProblem G) (candidate : CInputRef ctx (.unsignedWord width))
    (refs : AttemptRefs ctx width)
    (entry : Execution.Store ctx × (recoveryModel P oracles).HiddenState)
    {shape : CShape} (other : CInputRef ctx shape)
    (powerFree : refs.powerEqualsTarget.key ∉ other.storageKeys)
    (rawFree : refs.rawAccepted.key ∉ other.storageKeys)
    (acceptedFree : refs.acceptedCandidate.key ∉ other.storageKeys) :
    (verificationRecord (oracles := oracles) P candidate refs entry).1.1.read other =
      entry.1.read other := by
  exact (acceptanceRecord_preserves_read (oracles := oracles) P refs
    (powerCheckRecord (oracles := oracles) P candidate refs.powerEqualsTarget entry).1 other
    rawFree acceptedFree).trans
      (powerCheckRecord_preserves_read (oracles := oracles) P candidate refs.powerEqualsTarget
        entry other powerFree)

/-- Actual allocation, raw recovery and hidden group verification supply the exact
candidate and acceptance values to one caller continuation. The state equation
and value relation describe the same chronological record. -/
public lemma withAttempt_actualRecord_correct {ctx : RuntimeCtx .quantum}
    (P : KnownOrderProblem G)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (body : ∀ {inner : RuntimeCtx .quantum},
      CInputRef inner (.unsignedWord (OrderPreparation.width P)) →
      CInputRef inner .bit → ClassicalWorkspace.Transport ctx inner →
        Circuit (recoveryModel P oracles) inner inner)
    (Post : Execution.Store ctx → Execution.Store ctx →
      CShape.Value (.unsignedWord (OrderPreparation.width P)) → Bool → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx .quantum}
      (candidate : CInputRef inner (.unsignedWord (OrderPreparation.width P)))
      (accepted : CInputRef inner .bit)
      (transport : ClassicalWorkspace.Transport ctx inner),
      (∀ key ∈ candidate.storageKeys, ∀ {shape : CShape} (observed : CInputRef ctx shape),
        key ∉ (transport.liftInput observed).storageKeys) →
      (∀ key ∈ accepted.storageKeys, ∀ {shape : CShape} (observed : CInputRef ctx shape),
        key ∉ (transport.liftInput observed).storageKeys) →
      ∃ step : Execution.Store inner × (recoveryModel P oracles).HiddenState →
          (Execution.Store inner × (recoveryModel P oracles).HiddenState) ×
            (body candidate accepted transport).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference ((recoveryModel P oracles).HiddenState × History)),
          (body candidate accepted transport).execute
            (recoveryEnvironment P quantumEnvironment) Reference state =
            mapClassicalExplicit state (fun entry =>
              let result := step (entry.1, entry.2.1)
              (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
        ∀ before : Execution.Store inner × (recoveryModel P oracles).HiddenState,
          Post (transport.restrict before.1) (transport.restrict (step before).1.1)
            (before.1.read candidate) (before.1.read accepted).toBool) :
    ∃ step : Execution.Store ctx × (recoveryModel P oracles).HiddenState →
        (Execution.Store ctx × (recoveryModel P oracles).HiddenState) ×
          (withAttempt (oracles := oracles) P spec input body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference ((recoveryModel P oracles).HiddenState × History)),
        (withAttempt (oracles := oracles) P spec input body).execute
          (recoveryEnvironment P quantumEnvironment) Reference state =
          state.mapClassical (fun entry =>
            let result := step (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Execution.Store ctx × (recoveryModel P oracles).HiddenState,
        Post before.1 (step before).1.1
          (attemptCandidateValue spec (before.1.read input))
          (attemptAcceptedValue P spec (before.1.read input)) := by
  classical
  obtain ⟨step, equation, correct⟩ :=
    ClassicalWorkspace.withCells_actualRecord_initialized_restricted_post
      (environment := recoveryEnvironment P quantumEnvironment)
      (model := recoveryModel P oracles) ctx
      (attemptShapes (OrderPreparation.width P))
      (fun cells _ transport _ =>
        attemptBody (oracles := oracles) P spec (transport.liftInput input) (attemptRefs cells)
          (fun candidate accepted => body candidate accepted transport))
      (fun before after => Post before after
        (attemptCandidateValue spec (before.read input))
        (attemptAcceptedValue P spec (before.read input))) (by
        intro inner cells distinct transport separated
        let refs := attemptRefs cells
        have distinctRefs : (attemptKeys refs).Nodup := by
          rw [attemptKeys_cells]
          exact cells.workspaceCells_distinct_keys_nodup distinct
        have free : ∀ key ∈ attemptKeys refs,
            ∀ {shape : CShape} (observed : CInputRef ctx shape),
              key ∉ (transport.liftInput observed).storageKeys := by
          intro key present shape observed
          have actual : key ∈ cells.keys := by
            simpa only [refs, attemptKeys_cells] using present
          exact cells.workspaceCells_transportSeparated_avoids_of_mem
            transport separated actual observed
        let candidate : CInputRef inner (.unsignedWord (OrderPreparation.width P)) :=
          .storage refs.candidate.toCStorageRef
        let accepted : CInputRef inner .bit :=
          .storage refs.acceptedCandidate.toCStorageRef
        obtain ⟨bodyStep, bodyEquation, bodyPost⟩ := bodyContract candidate accepted transport
          (by
            intro key present shape observed
            simp only [candidate, CInputRef.storageKeys, List.mem_singleton] at present
            subst key
            exact free refs.candidate.key (by simp [attemptKeys]) observed)
          (by
            intro key present shape observed
            simp only [accepted, CInputRef.storageKeys, List.mem_singleton] at present
            subst key
            exact free refs.acceptedCandidate.key (by simp [attemptKeys]) observed)
        obtain ⟨rawStep, rawEquation, rawValues⟩ :=
          ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.singleIntoCells_actualRecord
            (environment := recoveryEnvironment P quantumEnvironment)
            (model := recoveryModel P oracles) spec (transport.liftInput input)
            refs.inverseSuccess refs.candidate refs.reconstruction
        let continued := body candidate accepted transport
        let tailStep := Circuit.sequenceRecord
          (powerCheck (oracles := oracles) P candidate refs.powerEqualsTarget)
          (.seq (acceptanceSuffix (oracles := oracles) P refs) continued)
          (powerCheckRecord (oracles := oracles) P candidate refs.powerEqualsTarget)
          (Circuit.sequenceRecord (acceptanceSuffix (oracles := oracles) P refs) continued
            (acceptanceRecord (oracles := oracles) P refs) bodyStep)
        have rawEquationExplicit :
            ∀ (Reference : Register) {History : Type} [Fintype History]
              (state : State inner Reference ((recoveryModel P oracles).HiddenState × History)),
              (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.singleIntoCells
                (model := recoveryModel P oracles) spec (transport.liftInput input)
                refs.inverseSuccess refs.candidate refs.reconstruction).execute
                  (recoveryEnvironment P quantumEnvironment) Reference state =
                mapClassicalExplicit state (fun entry =>
                  let result := rawStep (entry.1, entry.2.1)
                  (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
          intro Reference History _ state
          simpa only [mapClassicalExplicit] using rawEquation Reference state
        have powerEquationExplicit :
            ∀ (Reference : Register) {History : Type} [Fintype History]
              (state : State inner Reference ((recoveryModel P oracles).HiddenState × History)),
              (powerCheck (oracles := oracles) P candidate refs.powerEqualsTarget).execute
                (recoveryEnvironment P quantumEnvironment) Reference state =
                mapClassicalExplicit state (fun entry =>
                  let result := powerCheckRecord (oracles := oracles) P candidate
                    refs.powerEqualsTarget
                    (entry.1, entry.2.1)
                  (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
          intro Reference History _ state
          exact (powerCheck_execute (oracles := oracles) P candidate refs.powerEqualsTarget
            Reference state).trans
            (mapClassicalExplicit_eq state _).symm
        have composedEquation :=
          execute_sequenceRecord_explicit (model := recoveryModel P oracles) _ _ _ _
            rawEquationExplicit
            (execute_sequenceRecord_explicit (model := recoveryModel P oracles) _ _ _ _
              powerEquationExplicit
              (execute_sequenceRecord_explicit (model := recoveryModel P oracles) _ _ _ _
                (acceptanceSuffix_execute (oracles := oracles) P refs) bodyEquation))
        refine ⟨Circuit.sequenceRecord _ _ rawStep tailStep, ?_, ?_⟩
        · intro Reference History _ state
          exact (composedEquation Reference state).trans
            (mapClassicalExplicit_eq state _)
        · intro before _initialized
          let raw := ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells spec
            (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.preparationInput
              (before.1.read (transport.liftInput input)))
          have observed :
              (rawStep before).1.1.read (.storage refs.inverseSuccess.toCStorageRef) = raw.first ∧
              (rawStep before).1.1.read candidate = raw.second.first ∧
              (rawStep before).1.1.read (.storage refs.reconstruction.toCStorageRef) =
                raw.second.second := by
            rw [rawValues]
            exact raw_reads refs distinctRefs before.1 raw
          have rawOuter : transport.ReadsAs (transport.restrict before.1) (rawStep before).1.1 := by
            intro shape other
            rw [rawValues]
            exact (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.exposureWrite_read_other
              refs.inverseSuccess refs.candidate refs.reconstruction before.1 raw
              (transport.liftInput other)
              (free _ (by simp [attemptKeys]) other)
              (free _ (by simp [attemptKeys]) other)
              (free _ (by simp [attemptKeys]) other)).trans
                (transport.workspaceTransport_restrict_readsAs before.1 other)
          let checked := powerCheckRecord (oracles := oracles) P candidate
            refs.powerEqualsTarget (rawStep before).1
          let verified := acceptanceRecord (oracles := oracles) P refs checked.1
          have verifiedOuter : transport.ReadsAs (transport.restrict before.1) verified.1.1 := by
            intro shape other
            exact (verificationRecord_preserves_read (oracles := oracles) P candidate refs
              (rawStep before).1
              (transport.liftInput other)
              (free _ (by simp [attemptKeys]) other)
              (free _ (by simp [attemptKeys]) other)
              (free _ (by simp [attemptKeys]) other)).trans (rawOuter other)
          have candidateSame : verified.1.1.read candidate = raw.second.first := by
            exact (verificationRecord_preserves_read (oracles := oracles) P candidate refs
              (rawStep before).1 candidate
              (by
                simp only [candidate, CInputRef.storageKeys, List.mem_singleton]
                intro same
                simp [attemptKeys, same] at distinctRefs)
              (by
                simp only [candidate, CInputRef.storageKeys, List.mem_singleton]
                intro same
                simp [attemptKeys, same] at distinctRefs)
              (by
                simp only [candidate, CInputRef.storageKeys, List.mem_singleton]
                intro same
                simp [attemptKeys, same] at distinctRefs)).trans observed.2.1
          have acceptedValue : verified.1.1.read accepted =
              .bit (((raw.first.toBool && raw.second.second.toBool) &&
                decide (P.generator ^ raw.second.first.toNat = P.target))) := by
            have value := verificationRecord_value (oracles := oracles) P candidate refs
              (rawStep before).1
              (by
                simp only [candidate, CInputRef.storageKeys, List.mem_singleton]
                intro same
                simp [attemptKeys, same] at distinctRefs)
              (by
                simp only [CInputRef.storageKeys, List.mem_singleton]
                intro same
                simp [attemptKeys, same] at distinctRefs)
              (by
                simp only [CInputRef.storageKeys, List.mem_singleton]
                intro same
                simp [attemptKeys, same] at distinctRefs)
              (by
                intro same
                simp [attemptKeys, same] at distinctRefs)
            rw [observed.1, observed.2.1, observed.2.2] at value
            exact value
          have following := bodyPost verified.1
          have unchanged := transport.workspaceTransport_readsAs_restrict_iff.mp verifiedOuter
          rw [unchanged, candidateSame, acceptedValue, CShape.Value.toBool] at following
          have inputRead := transport.workspaceTransport_restrict_readsAs before.1 input
          simp only [Circuit.sequenceRecord, tailStep, checked, verified,
            continued, attemptCandidateValue, attemptAcceptedValue, raw, inputRead] at following ⊢
          convert following using 1
          congr 1
    )
  exact ⟨step, equation, correct⟩

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
