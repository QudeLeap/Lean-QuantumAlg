/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Protection
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Scope
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Packing
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Initialization
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Specification

/-!
# Conditional contraction through the same actual feedback factory

All three attempts execute. The original seven checker cells are retained
once, while the one real feedback scope is allocated and released around
the actual loop. The internal support includes both nominal points, the four
original constants and all thirty-four signed base rows. Candidate-mass and support obligations are
internal conditional hypotheses about this same preparation. No sampling
Born theorem or unconditional final algorithm success is asserted here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve CandidateCheck.Native
open ClassicalRoutines.EllipticCurve.WindowTables ClassicalRoutines.Modular.NativePower

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

namespace Conditional

private lemma mapped_supported {Original Result : Type} [Fintype Original] [Fintype Result]
    {R : Register} (decision : DecidableEq Result) (state : ExecutionState Original R)
    (update : Original → Result) (before : Original → Prop) (after : Result → Prop)
    (supported : ∀ original, 0 < (state.block original).mass → before original)
    (preserved : ∀ original, before original → after (update original)) :
    ∀ result, 0 < ((@ExecutionState.mapClassical Original Result _ _ R decision
      state update).block result).mass → after result := by
  cases Subsingleton.elim decision (Classical.decEq Result)
  intro result positive
  obtain ⟨original, same, prior⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff state update result).mp positive
  exact same ▸ preserved original (supported original prior)

private lemma inputsSupported_push {outer inner : RuntimeCtx .quantum} {Reference : Register}
    {Label : Type} [Fintype Label] (original : Inputs outer) (lift : Transport outer inner)
    (basePoint targetPoint : Pure.Point original.curve) (state : State inner Reference Label)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (supported : inputsSupported original lift basePoint targetPoint state) :
    inputsSupported original (lift.underWorkspace key shape fresh) basePoint targetPoint
      (state.pushWorkspace key shape fresh) := by
  rw [State.state_pushWorkspace_as_mapClassical]
  apply mapped_supported
  · exact supported
  · intro before prior
    apply (readConditions_congr original basePoint targetPoint _ _ ?_).mp prior
    intro observed input
    rw [Transport.liftInput_underWorkspace, Store.read_pushWorkspace_underWorkspace]

private lemma inputsSupported_mapHistory {outer inner : RuntimeCtx .quantum}
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K] (original : Inputs outer)
    (lift : Transport outer inner) (basePoint targetPoint : Pure.Point original.curve)
    (state : State inner Reference H) (update : H → K)
    (supported : inputsSupported original lift basePoint targetPoint state) :
    inputsSupported original lift basePoint targetPoint (State.mapHistory state update) := by
  unfold State.mapHistory
  exact mapped_supported _ state _ _ _ supported (fun _ prior => prior)

private def flagBound {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (lift : Transport outer inner)
    (basePoint targetPoint : Pure.Point original.curve) (input : CInputRef inner .bit) (factor : ℝ)
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)),
    inputsSupported original lift basePoint targetPoint state →
    CheckerTail.readWeight (code.execute environment Reference state) (flagInputRead input) false ≤
      factor * CheckerTail.readWeight state (flagInputRead input) false

private lemma workspace_bound {outer inner : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs outer) (lift : Transport outer inner)
    (basePoint targetPoint : Pure.Point original.curve) (input : CInputRef inner .bit) (factor : ℝ)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (bodyBound : flagBound original (lift.underWorkspace key shape fresh) basePoint targetPoint
      (input.underWorkspace key shape fresh) factor body environment) :
    flagBound original lift basePoint targetPoint input factor
      (Circuit.workspace (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        inner key shape fresh body) environment := by
  intro Reference History _ state supported
  rw [Circuit.execute_workspace, feedback_pop_flag_weight]
  have bound := bodyBound (state.pushWorkspace key shape fresh)
    (inputsSupported_push original lift basePoint targetPoint state key shape fresh supported)
  exact bound.trans_eq (congrArg (fun weight : ℝ => factor * weight)
    (feedback_push_flag_weight state key shape fresh input false))

private lemma compose_underWorkspace {first middle last : RuntimeCtx .quantum}
    (head : Transport first middle) (tail : Transport middle last)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ last.keys) :
    head.compose (tail.underWorkspace key shape fresh) =
      (head.compose tail).underWorkspace key shape fresh := rfl

private lemma compose_id {outer inner : RuntimeCtx .quantum} (lift : Transport outer inner) :
    lift.compose (Transport.id inner) = lift := by
  cases lift
  rfl

private lemma withFrame_bound {outer ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (initialLift : Transport outer ctx)
    (basePoint targetPoint : Pure.Point original.curve) (input : CInputRef ctx .bit)
    (wordWidth parityCount : Nat) (factor : ℝ)
    (body : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner),
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      (scratch : Frame inner wordWidth parityCount) → CallerFree scratch lift →
      Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (scratch : Frame inner wordWidth parityCount) (fresh : CallerFree scratch lift),
      flagBound original (initialLift.compose lift) basePoint targetPoint
        (lift.liftInput input) factor (body lift same scratch fresh) environment) :
    flagBound original initialLift basePoint targetPoint input factor
      (withFrame (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx wordWidth parityCount body) environment := by
  have actual : flagBound original (initialLift.compose (Transport.id ctx))
      basePoint targetPoint ((Transport.id ctx).liftInput input) factor
      (withFrame (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx wordWidth parityCount body) environment := withCellsWithQuantumWiresFrom_property
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (Transport.id ctx) rfl
    (shapes wordWidth parityCount)
    (fun cells distinct lift separated same =>
      body lift (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
        (ofCells_callerFree cells distinct lift separated))
    (fun lift _ code => flagBound original (initialLift.compose lift) basePoint targetPoint
      (lift.liftInput input) factor code environment)
    (by
      intro inner lift same key shape fresh code established
      apply workspace_bound original (initialLift.compose lift) basePoint targetPoint
        (lift.liftInput input) factor key shape fresh code environment
      intro Reference History finite state supported
      have currentSupport : inputsSupported original
          (initialLift.compose (lift.underWorkspace key shape fresh))
          basePoint targetPoint state := by
        simpa only [compose_underWorkspace] using supported
      have returned := @established Reference History finite state currentSupport
      simpa only [Transport.liftInput_underWorkspace] using returned)
    (by
      intro inner cells distinct lift separated same Reference History finite state supported
      exact @bodyBound inner lift (quantumLayout_wires_of_quantumWires same)
        (Frame.ofCells cells distinct) (ofCells_callerFree cells distinct lift separated)
        Reference History finite state supported)
  intro Reference History finite state supported
  have currentSupport : inputsSupported original (initialLift.compose (Transport.id ctx))
      basePoint targetPoint state := by
    simpa only [compose_id] using supported
  have returned := @actual Reference History finite state currentSupport
  simpa only [Transport.liftInput_id] using returned

end Conditional

namespace Inputs

variable {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (lift : Transport (persistentCtx outer 256 260) inner)
    (same : (persistentCtx outer 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private def retainedInput : Inputs (persistentCtx outer 256 260) :=
  original.transport (Recovery.persistentTransport outer) (Recovery.persistent_wires outer)

private def currentInput : Inputs inner := (original.retainedInput).transport lift same

private def currentSampler : Sampling.Parameters inner :=
  (original.retainedInput).samplerParameters lift same scratch fresh

private def currentCheckers : Checkers inner := (Checkers.retained outer).transport lift

private def currentAccepted : CInputRef inner .bit :=
  .storage (currentCheckers lift).accepted.toCStorageRef

private def CurrentSupport (basePoint targetPoint : Pure.Point original.curve)
    {Reference : Register} {Label : Type} [Fintype Label]
    (state : State inner Reference Label) : Prop :=
  Conditional.inputsSupported original ((Recovery.persistentTransport outer).compose lift)
    basePoint targetPoint state

private def PreparedSupport (basePoint targetPoint : Pure.Point original.curve) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)),
    original.CurrentSupport lift basePoint targetPoint state →
    original.CurrentSupport lift basePoint targetPoint
      (((original.currentInput lift same).preparation
        (original.currentSampler lift same scratch fresh)).execute environment Reference state)

private def CandidateMass (basePoint targetPoint : Pure.Point original.curve) (lower : ℝ) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)),
    original.CurrentSupport lift basePoint targetPoint state →
    lower * CheckerTail.readWeight state (flagInputRead (currentAccepted lift)) false ≤
      CheckerTail.readWeight
        (((original.currentInput lift same).preparation
          (original.currentSampler lift same scratch fresh)).execute environment Reference
            (state.selectClassical
              (fun before => flagInputRead (currentAccepted lift) before.1) false))
        (((original.currentInput lift same).checkerTail
          (original.currentSampler lift same scratch fresh) (currentCheckers lift)).eligibleBit
            basePoint targetPoint) true

private lemma fresh_attempt_bound (basePoint targetPoint : Pure.Point original.curve)
    (lower : ℝ)
    (prepared : original.PreparedSupport lift same scratch fresh environment basePoint targetPoint)
    (quality : original.CandidateMass lift same scratch fresh environment basePoint targetPoint
      lower) :
    Conditional.flagBound original ((Recovery.persistentTransport outer).compose lift)
      basePoint targetPoint
      (currentAccepted lift) (1 - lower)
      ((original.currentInput lift same).attempt
        (original.currentSampler lift same scratch fresh) (currentCheckers lift))
      environment := by
  intro Reference History _ state supported
  have separated := original.transported_checker_separation lift same
  have contraction := (original.currentInput lift same).attempt_failure_le
    (original.currentSampler lift same scratch fresh) (currentCheckers lift)
    environment lower basePoint targetPoint separated.1 separated.2.1 separated.2.2 state
    (by
      intro entry positive
      have facts := (prepared state supported) entry positive
      simpa only [checkerTail, currentInput, retainedInput, transport,
        Transport.liftInput_compose] using facts.1)
  apply contraction
  · exact (original.retainedInput).fresh_preparation_flag_weight lift same scratch fresh
      environment (Checkers.retained outer).accepted.toCStorageRef false state
  · have candidate := (original.retainedInput).fresh_preparation_candidate_weight
      lift same scratch fresh environment (Checkers.retained outer).accepted.toCStorageRef
      (((original.currentInput lift same).checkerTail
        (original.currentSampler lift same scratch fresh) (currentCheckers lift)).eligibleBit
          basePoint targetPoint) state
    exact (quality state supported).trans_eq candidate.symm


private lemma fresh_checker_supported (basePoint targetPoint : Pure.Point original.curve)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History))
    (supported : original.CurrentSupport lift basePoint targetPoint state) :
    original.CurrentSupport lift basePoint targetPoint
      ((((original.currentInput lift same).checkerTail
        (original.currentSampler lift same scratch fresh) (currentCheckers lift)).code
          (services := services)).execute environment Reference state) := by
  obtain ⟨record, actual, returned⟩ := (original.currentInput lift same).checker_actualRecord
    (original.currentSampler lift same scratch fresh) (currentCheckers lift) environment
  rw [actual]
  apply Conditional.mapped_supported
  · exact supported
  · intro before prior
    apply (Conditional.readConditions_congr original basePoint targetPoint _ _ ?_).mp prior
    intro shape observed
    have preserved := original.transported_checker_preserves_read lift same
      (original.currentSampler lift same scratch fresh) environment (before.1, before.2.1) observed
    have actualRead : (record (before.1, before.2.1)).1.1.read
        (((Recovery.persistentTransport outer).compose lift).liftInput observed) =
      before.1.read (((Recovery.persistentTransport outer).compose lift).liftInput observed) := by
      rw [returned]
      simpa only [checkerStore, currentInput, retainedInput, currentCheckers,
        Transport.liftInput_compose] using preserved
    exact actualRead.symm

private lemma fresh_attempt_supported (basePoint targetPoint : Pure.Point original.curve)
    (prepared : original.PreparedSupport lift same scratch fresh environment basePoint targetPoint)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History))
    (supported : original.CurrentSupport lift basePoint targetPoint state) :
    original.CurrentSupport lift basePoint targetPoint
      (((original.currentInput lift same).attempt
        (original.currentSampler lift same scratch fresh) (currentCheckers lift)).execute
          environment Reference state) := by
  rw [(original.currentInput lift same).attempt_code_eq
    (original.currentSampler lift same scratch fresh) (currentCheckers lift)]
  rw [Circuit.execute_seq]
  apply Conditional.inputsSupported_mapHistory
  exact original.fresh_checker_supported lift same scratch fresh environment
    basePoint targetPoint _ (prepared state supported)

private lemma fresh_loop_bound (basePoint targetPoint : Pure.Point original.curve)
    (count : Nat) (lower : ℝ) (atMostOne : lower ≤ 1)
    (prepared : original.PreparedSupport lift same scratch fresh environment basePoint targetPoint)
    (quality : original.CandidateMass lift same scratch fresh environment basePoint targetPoint
      lower) :
    Conditional.flagBound original ((Recovery.persistentTransport outer).compose lift)
      basePoint targetPoint
      (currentAccepted lift) ((1 - lower) ^ count)
      (Circuit.forRange count fun _ => (original.currentInput lift same).attempt
        (original.currentSampler lift same scratch fresh) (currentCheckers lift)) environment := by
  intro Reference History _ state supported
  have loop := (original.currentInput lift same).attempts_failure_le_of_internal_evidence
    (original.currentSampler lift same scratch fresh) (currentCheckers lift) environment Reference
    (fun {_} [_] current => original.CurrentSupport lift basePoint targetPoint current)
    count lower atMostOne
  apply loop
  · intro nextHistory _ nextState nextSupported
    exact original.fresh_attempt_supported lift same scratch fresh environment basePoint targetPoint
      prepared nextState nextSupported
  · intro nextHistory _ nextState nextSupported
    exact original.fresh_attempt_bound lift same scratch fresh environment basePoint targetPoint
      lower prepared quality nextState nextSupported
  · exact supported

end Inputs

namespace Inputs

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private def InternalPreparation (basePoint targetPoint : Pure.Point original.curve) : Prop :=
  ∀ {inner : RuntimeCtx .quantum} (lift : Transport (persistentCtx ctx 256 260) inner)
    (same : (persistentCtx ctx 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift),
    original.PreparedSupport lift same scratch fresh environment basePoint targetPoint

private def InternalCandidateMass (basePoint targetPoint : Pure.Point original.curve)
    (lower : ℝ) : Prop :=
  ∀ {inner : RuntimeCtx .quantum} (lift : Transport (persistentCtx ctx 256 260) inner)
    (same : (persistentCtx ctx 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift),
    original.CandidateMass lift same scratch fresh environment basePoint targetPoint lower

/-- Conditional failure contraction for the literal one-scope loop and same seven destinations. -/
lemma scoped_attempts_failure_le_of_internal_evidence
    (basePoint targetPoint : Pure.Point original.curve) (count : Nat) (lower : ℝ)
    (atMostOne : lower ≤ 1)
    (prepared : original.InternalPreparation environment basePoint targetPoint)
    (quality : original.InternalCandidateMass environment basePoint targetPoint lower) :
    Conditional.flagBound original (Recovery.persistentTransport ctx) basePoint targetPoint
      (.storage (Checkers.retained ctx).accepted.toCStorageRef) ((1 - lower) ^ count)
      (original.scopedAttempts (services := services) count) environment := by
  exact Conditional.withFrame_bound original (Recovery.persistentTransport ctx)
    basePoint targetPoint
    (.storage (Checkers.retained ctx).accepted.toCStorageRef) 256 256 ((1 - lower) ^ count)
    (fun lift same scratch fresh => Circuit.forRange count fun _ =>
      (original.currentInput lift same).attempt
        (original.currentSampler lift same scratch fresh) (currentCheckers lift))
    environment (fun lift same scratch fresh =>
      original.fresh_loop_bound lift same scratch fresh environment basePoint targetPoint
        count lower
        atMostOne (prepared lift same scratch fresh) (quality lift same scratch fresh))


private lemma persistent_transport_input {shape : CShape} (input : CInputRef ctx shape) :
    (Recovery.persistentTransport ctx).liftInput input = persistentInput 256 260 input := by
  induction input with
  | storage ref => rfl
  | product left right leftIH rightIH => exact congrArg₂ CInputRef.product leftIH rightIH
  | fixedVector entries entriesIH => exact congrArg CInputRef.fixedVector (funext entriesIH)
  | first input ih => exact congrArg CInputRef.first ih
  | second input ih => exact congrArg CInputRef.second ih
  | vectorGet input index ih => exact congrArg (fun source => CInputRef.vectorGet source index) ih
  | bitsGet input index ih => exact congrArg (fun source => CInputRef.bitsGet source index) ih
  | wordBitGet input index ih => exact congrArg (fun source => CInputRef.wordBitGet source index) ih

private lemma retained_inputs_supported (basePoint targetPoint : Pure.Point original.curve)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : Conditional.inputsSupported original (Transport.id ctx)
      basePoint targetPoint state) :
    Conditional.inputsSupported original (Recovery.persistentTransport ctx)
      basePoint targetPoint
      ((retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx 256 260).execute environment Reference state) := by
  rw [retainPersistent_execute]
  unfold persistentAllocationState
  apply Conditional.mapped_supported
  · exact supported
  · intro before prior
    apply (Conditional.readConditions_congr original basePoint targetPoint _ _ ?_).mp prior
    intro shape observed
    have unchanged := persistentInitialStore_read 256 260 before.1 observed
    simpa only [Transport.liftInput_id, persistent_transport_input, persistentAllocationStep]
      using unchanged.symm

private def RunFailureBound (basePoint targetPoint : Pure.Point original.curve)
    (lower : ℝ) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    Conditional.inputsSupported original (Transport.id ctx) basePoint targetPoint state →
    ((original.run (services := services)).code.execute environment Reference state).effectWeight
        (fun entry => if entry.1.read (batchResultRead ctx 256 260) = .optionNone then
          Effect.one ((batchResultCtx ctx 256 260).register.prod Reference)
        else Effect.zero ((batchResultCtx ctx 256 260).register.prod Reference)) ≤
      (1 - lower) ^ 3 * state.mass

/-- The same actual factory's absent-result bound, conditional only on its internal evidence.

This is not a final Born or algorithm theorem. All original constant, signed-base and nominal
point reads, together with the checked-candidate mass, are internal obligations of the same
actual preparation. The final caller receives no additional support or sampling-floor premise.
-/
lemma storage_run_failure_le_of_internal_evidence
    (basePoint targetPoint : Pure.Point original.curve) (lower : ℝ) (atMostOne : lower ≤ 1)
    (prepared : original.InternalPreparation environment basePoint targetPoint)
    (quality : original.InternalCandidateMass environment basePoint targetPoint lower) :
    original.RunFailureBound environment basePoint targetPoint lower := by
  intro Reference History _ state supported
  have packed := original.storage_run_none_weight environment state
  have sequential := stored_weight_seq
    (retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx 256 260) (original.scopedAttempts (services := services) 3) environment state
    (fun store => flagEffect ((persistentCtx ctx 256 260).register.prod Reference)
      (flagInputRead (.storage (Checkers.retained ctx).accepted.toCStorageRef) store) false)
  have scopeBound := original.scoped_attempts_failure_le_of_internal_evidence environment
    basePoint targetPoint 3 lower atMostOne prepared quality
    ((retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx 256 260).execute environment Reference state)
    (original.retained_inputs_supported environment basePoint targetPoint state supported)
  have initial := retainPersistent_failure_weight
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (environment := environment) 256 260 state
  exact ((packed.trans sequential).le.trans scopeBound).trans_eq
    (congrArg (fun weight : ℝ => (1 - lower) ^ 3 * weight) initial)

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
