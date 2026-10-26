/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Soundness.Scope
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized.Validity

/-! # Sound present outputs of the actual finalized recovery run -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
namespace Storage

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve CandidateCheck.Native

noncomputable section
local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma cleanup_scalar_property {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (cleanup : Cleanup.Parameters ctx)
    (selected : CStorageRef ctx (.unsignedWord 260))
    (property : CShape.Value (.unsignedWord 260) → Prop)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      property (entry.1.read (.storage selected))) :
    ∀ entry, 0 < (((Circuit.embed (allowAllocation := true)
      (ContextEmbedding.identity ctx) cleanup.circuit).execute
      environment Reference state).block entry).mass →
      property (entry.1.read (.storage selected)) := by
  classical
  have chosen : SelectsRead (originalStorageRead selected (fun value => decide (property value)))
      true (Circuit.embed (allowAllocation := true)
        (ContextEmbedding.identity ctx) cleanup.circuit) environment := by
    apply selects_read_identity_embed
    exact reset_selects_storage cleanup ctx.systemCount id selected
      (fun value => decide (property value)) true
      (by intro cardinality impossible; cases impossible) environment
  have preserved := selects_read_preserves_positive
    (originalStorageRead selected (fun value => decide (property value))) true
    (Circuit.embed (allowAllocation := true) (ContextEmbedding.identity ctx) cleanup.circuit)
    environment chosen state (fun entry positive => decide_eq_true (supported entry positive))
  exact fun entry positive => of_decide_eq_true (preserved entry positive)

private def CleanupSoundnessStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {curve : CurveSpec 256} (cleanup : Cleanup.Parameters ctx)
    (accepted : CStorageRef ctx .bit) (selected : CStorageRef ctx (.unsignedWord 260))
    (basePoint targetPoint : Pure.Point curve)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (_supported : ∀ entry, 0 < (state.block entry).mass →
      Inputs.latchSound (.storage accepted) (.storage selected) basePoint targetPoint entry.1),
    ∀ entry, 0 < (((Circuit.embed (allowAllocation := true)
      (ContextEmbedding.identity ctx) cleanup.circuit).execute
        environment Reference state).block entry).mass →
      Inputs.latchSound (.storage accepted) (.storage selected) basePoint targetPoint entry.1

private lemma cleanup_soundness : CleanupSoundnessStatement := by
  intro ctx services curve cleanup accepted selected basePoint targetPoint environment
    Reference History finite state supported
  apply selects_read_preserves_implication (bitRead accepted)
    (fun store => (store.read (.storage selected)).toNat • basePoint = targetPoint)
    (Circuit.embed (allowAllocation := true) (ContextEmbedding.identity ctx) cleanup.circuit)
    environment ?_ ?_ state supported
  · apply selects_read_identity_embed
    exact reset_selects_bit cleanup ctx.systemCount id accepted true environment
  · intro currentReference currentHistory currentFinite current prior
    exact cleanup_scalar_property (ctx := ctx) (services := services) cleanup selected
      (fun value => value.toNat • basePoint = targetPoint) environment current prior

namespace Inputs

private def FreshFinalizedSoundnessStatement : Prop :=
  ∀ {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (lift : Transport (persistentCtx outer 256 260) inner)
    (same : (persistentCtx outer 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (basePoint targetPoint : Pure.Point original.curve) (count : Nat)
    (_prepared : original.PreparedSupport lift same scratch fresh environment basePoint
      targetPoint),
    SoundBound original ((Recovery.persistentTransport outer).compose lift) basePoint targetPoint
      (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
      ((original.currentInput lift same).finalizedInnerBody (services := services)
        (original.currentSampler lift same scratch fresh) (currentCheckers lift) count) environment

private lemma fresh_finalized_soundness : FreshFinalizedSoundnessStatement := by
  intro outer inner services original lift same scratch fresh environment basePoint targetPoint
      count
    prepared Reference History finite state supported sound
  apply Circuit.supported_store_seq environment
    (Circuit.forRange count fun _ => (original.currentInput lift same).attempt (services :=
      services)
      (original.currentSampler lift same scratch fresh) (currentCheckers lift))
    (Circuit.embed (ContextEmbedding.identity inner)
      (finalizedCleanup (original.currentSampler lift same scratch fresh)).circuit)
    Reference state
    (latchSound (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
      basePoint targetPoint)
  apply cleanup_soundness (ctx := inner) (services := services)
    (finalizedCleanup (original.currentSampler lift same scratch fresh))
    (currentCheckers lift).accepted.toCStorageRef (currentCheckers lift).selected.toCStorageRef
    basePoint targetPoint environment
  exact fresh_loop_soundness (outer := outer) (inner := inner) (services := services)
    original lift same scratch fresh environment basePoint targetPoint count prepared state
    supported sound

attribute [local irreducible] withFrame

/-- Actual lexical feedback allocation retains the original checked scalar equation. -/
lemma scopedAttemptsFinalized_soundness {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (basePoint targetPoint : Pure.Point original.curve) (count : Nat)
    (prepared : original.InternalPreparation environment basePoint targetPoint) :
    SoundBound original (Recovery.persistentTransport ctx) basePoint targetPoint
      (.storage (Checkers.retained ctx).accepted.toCStorageRef)
      (.storage (Checkers.retained ctx).selected.toCStorageRef)
      (original.scopedAttemptsFinalized (services := services) count) environment := by
  unfold scopedAttemptsFinalized
  exact withFrame_sound (ctx := persistentCtx ctx 256 260) (services := services)
    original (Recovery.persistentTransport ctx) basePoint targetPoint
    (.storage (Checkers.retained ctx).accepted.toCStorageRef)
    (.storage (Checkers.retained ctx).selected.toCStorageRef) 256 256
    (fun lift same scratch fresh =>
      (original.currentInput lift same).finalizedInnerBody (services := services)
        (original.currentSampler lift same scratch fresh) (currentCheckers lift) count)
    environment (fun lift same scratch fresh =>
      fresh_finalized_soundness (services := services) original lift same scratch fresh
        environment basePoint targetPoint count (prepared lift same scratch fresh))

private lemma retained_latch_sound {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} {curve : CurveSpec 256}
    (basePoint targetPoint : Pure.Point curve)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    ∀ entry, 0 < (((retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260).execute
        environment Reference state).block entry).mass →
      latchSound (.storage (Checkers.retained ctx).accepted.toCStorageRef)
        (.storage (Checkers.retained ctx).selected.toCStorageRef) basePoint targetPoint entry.1
      := by
  intro entry positive accepted
  have initial := retainPersistent_latches_supported
    (environment := environment) 256 260 state entry positive
  change (entry.1.read (.storage (persistentAccepted ctx 256 260).toCStorageRef)).toBool = true
    at accepted
  rw [initial.1] at accepted
  change false = true at accepted
  cases accepted

private def RunFinalizedSomeSoundStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (basePoint targetPoint : Pure.Point original.curve)
    (_prepared : original.InternalPreparation environment basePoint targetPoint)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (_supported : Conditional.inputsSupported original (Transport.id ctx)
      basePoint targetPoint state),
    ∀ entry, 0 < (((original.runFinalized (services := services)).code.execute
      environment Reference state).block entry).mass →
      ∀ value, entry.1.read (batchResultRead ctx 256 260) = .optionSome value →
        value.toNat • basePoint = targetPoint

private lemma runFinalizedSomeSound_proof : RunFinalizedSomeSoundStatement := by
  intro ctx services original environment basePoint targetPoint prepared
    Reference History finite state supported
  let retained := retainPersistent
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
  let loop := original.scopedAttemptsFinalized (services := services) 3
  have retainedSound := retained_latch_sound (ctx := ctx) (services := services)
    basePoint targetPoint environment state
  have retainedSupport := original.retained_inputs_supported environment
    basePoint targetPoint state supported
  have prefixSound := Circuit.supported_store_seq environment retained loop Reference state
    (latchSound (.storage (Checkers.retained ctx).accepted.toCStorageRef)
      (.storage (Checkers.retained ctx).selected.toCStorageRef) basePoint targetPoint)
    (original.scopedAttemptsFinalized_soundness (services := services) environment
      basePoint targetPoint 3 prepared (retained.execute environment Reference state)
      retainedSupport retainedSound)
  apply Circuit.supported_store_seq environment (retained.seq loop)
    (packBatchResult (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx 256 260) Reference state
    (fun store => ∀ value, store.read (batchResultRead ctx 256 260) = .optionSome value →
      value.toNat • basePoint = targetPoint)
  intro entry positive value output
  exact packBatchResult_supported_property (environment := environment)
    (fun value => value.toNat • basePoint = targetPoint)
    ((retained.seq loop).execute environment Reference state)
    (fun before present accepted => prefixSound before present accepted) entry positive value output

/-- Every present actual finalized result satisfies the original checked group equation. -/
lemma runFinalized_some_sound {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (basePoint targetPoint : Pure.Point original.curve)
    (prepared : original.InternalPreparation environment basePoint targetPoint)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : Conditional.inputsSupported original (Transport.id ctx)
      basePoint targetPoint state) :
    ∀ entry, 0 < (((original.runFinalized (services := services)).code.execute
      environment Reference state).block entry).mass →
      ∀ value, entry.1.read (batchResultRead ctx 256 260) = .optionSome value →
        value.toNat • basePoint = targetPoint := by
  exact runFinalizedSomeSound_proof (ctx := ctx) (services := services) original environment
    basePoint targetPoint prepared (Reference := Reference) (History := History) state supported

/-- A present actual finalized result is bounded and satisfies the same original point check. -/
lemma runFinalized_some_valid {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (basePoint targetPoint : Pure.Point original.curve)
    (prepared : original.InternalPreparation environment basePoint targetPoint)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : Conditional.inputsSupported original (Transport.id ctx)
      basePoint targetPoint state) :
    ∀ entry, 0 < (((original.runFinalized (services := services)).code.execute
      environment Reference state).block entry).mass →
      ∀ value, entry.1.read (batchResultRead ctx 256 260) = .optionSome value →
        value.toNat < original.order.modulus ∧ value.toNat • basePoint = targetPoint := by
  intro entry positive value output
  exact ⟨original.runFinalized_some_lt environment state entry positive value output,
    original.runFinalized_some_sound environment basePoint targetPoint prepared state supported
      entry positive value output⟩

end Inputs
end
end Storage
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
