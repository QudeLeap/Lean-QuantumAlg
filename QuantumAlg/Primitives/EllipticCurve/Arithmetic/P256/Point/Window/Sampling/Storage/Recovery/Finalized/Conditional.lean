/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Conditional
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized

/-!
# Conditional failure bound for the actual terminal-cleanup run

The same three attempts execute before actual all-bank terminal cleanup and
the unchanged optional-result packing. The result remains conditional on the
original complete input support, preparation support, and internal candidate
mass. It does not assert a sampling floor or a Born theorem.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve CandidateCheck.Native

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma finalized_cleanup_weight_eq {inner : RuntimeCtx .quantum}
    {services : ClassicalOracleModel}
    (loop : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner)
    (cleanup : Cleanup.Parameters inner) (observed : CStorageRef inner .bit)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)) :
    CheckerTail.readWeight
      ((loop.seq (Circuit.embed (ContextEmbedding.identity inner) cleanup.circuit)).execute
        environment Reference state) (flagInputRead (.storage observed)) false =
      CheckerTail.readWeight (loop.execute environment Reference state)
        (flagInputRead (.storage observed)) false := by
  let embedded : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      inner inner := Circuit.embed (ContextEmbedding.identity inner) cleanup.circuit
  have sequential :
      CheckerTail.readWeight ((loop.seq embedded).execute environment Reference state)
        (flagInputRead (.storage observed)) false =
      CheckerTail.readWeight
        (embedded.execute environment Reference (loop.execute environment Reference state))
        (flagInputRead (.storage observed)) false := by
    unfold CheckerTail.readWeight
    exact stored_weight_seq loop embedded environment state
      (fun store => flagEffect (inner.register.prod Reference)
        (flagInputRead (.storage observed) store) false)
  have identity :
      CheckerTail.readWeight
        (embedded.execute environment Reference (loop.execute environment Reference state))
        (flagInputRead (.storage observed)) false =
      CheckerTail.readWeight
        (cleanup.circuit.execute environment Reference (loop.execute environment Reference state))
        (flagInputRead (.storage observed)) false := by
    rw [Circuit.execute_identity_embed]
  have preserved := cleanup_circuit_flag_weight (services := services) cleanup observed
    false environment (loop.execute environment Reference state)
  exact sequential.trans (identity.trans preserved)

private lemma finalized_cleanup_contraction {inner : RuntimeCtx .quantum}
    {services : ClassicalOracleModel}
    (loop : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner)
    (cleanup : Cleanup.Parameters inner) (observed : CStorageRef inner .bit)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)) (factor : ℝ)
    (loopBound :
      CheckerTail.readWeight (loop.execute environment Reference state)
        (flagInputRead (.storage observed)) false ≤
      factor * CheckerTail.readWeight state
        (flagInputRead (.storage observed)) false) :
    CheckerTail.readWeight
      ((loop.seq (Circuit.embed (ContextEmbedding.identity inner) cleanup.circuit)).execute
        environment Reference state) (flagInputRead (.storage observed)) false ≤
      factor * CheckerTail.readWeight state
        (flagInputRead (.storage observed)) false := by
  have same := finalized_cleanup_weight_eq loop cleanup observed environment state
  exact same.le.trans loopBound

private lemma finalized_body_contraction_of_loop_bound {inner : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (inputs : Inputs inner)
    (sampler : Sampling.Parameters inner) (checkers : Checkers inner) (count : Nat)
    (observed : CStorageRef inner .bit)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)) (factor : ℝ)
    (loopBound :
      CheckerTail.readWeight
        ((Circuit.forRange count fun _ => inputs.attempt (services := services)
          sampler checkers).execute environment Reference state)
        (flagInputRead (.storage observed)) false ≤
      factor * CheckerTail.readWeight state
        (flagInputRead (.storage observed)) false) :
    CheckerTail.readWeight
      ((inputs.finalizedInnerBody (services := services) sampler checkers count).execute
        environment Reference state) (flagInputRead (.storage observed)) false ≤
      factor * CheckerTail.readWeight state
        (flagInputRead (.storage observed)) false := by
  unfold Inputs.finalizedInnerBody
  exact finalized_cleanup_contraction
    (Circuit.forRange count fun _ => inputs.attempt (services := services) sampler checkers)
    (Inputs.finalizedCleanup sampler) observed environment state factor loopBound

namespace Inputs

variable {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (lift : Transport (persistentCtx outer 256 260) inner)
    (same : (persistentCtx outer 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private lemma fresh_finalized_loop_bound (basePoint targetPoint : Pure.Point original.curve)
    (count : Nat) (lower : ℝ) (atMostOne : lower ≤ 1)
    (prepared : original.PreparedSupport lift same scratch fresh environment basePoint targetPoint)
    (quality : original.CandidateMass lift same scratch fresh environment basePoint targetPoint
      lower) :
    Conditional.flagBound original ((Recovery.persistentTransport outer).compose lift)
      basePoint targetPoint (currentAccepted lift) ((1 - lower) ^ count)
      ((original.currentInput lift same).finalizedInnerBody
        (services := services) (original.currentSampler lift same scratch fresh)
        (currentCheckers lift) count) environment := by
  intro Reference History _ state supported
  have loopBound := original.fresh_loop_bound lift same scratch fresh environment
    basePoint targetPoint count lower atMostOne prepared quality state supported
  exact finalized_body_contraction_of_loop_bound
    (original.currentInput lift same)
    (original.currentSampler lift same scratch fresh) (currentCheckers lift) count
    (currentCheckers lift).accepted.toCStorageRef environment state ((1 - lower) ^ count)
    loopBound

end Inputs

namespace Inputs

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

/-- Conditional contraction for the actual scoped loop followed by all-bank cleanup. -/
lemma scopedAttemptsFinalized_failure_le_of_internal_evidence
    (basePoint targetPoint : Pure.Point original.curve) (count : Nat) (lower : ℝ)
    (atMostOne : lower ≤ 1)
    (prepared : original.InternalPreparation environment basePoint targetPoint)
    (quality : original.InternalCandidateMass environment basePoint targetPoint lower) :
    Conditional.flagBound original (Recovery.persistentTransport ctx) basePoint targetPoint
      (.storage (Checkers.retained ctx).accepted.toCStorageRef) ((1 - lower) ^ count)
      (original.scopedAttemptsFinalized (services := services) count) environment := by
  exact Conditional.withFrame_bound original (Recovery.persistentTransport ctx)
    basePoint targetPoint
    (.storage (Checkers.retained ctx).accepted.toCStorageRef) 256 256 ((1 - lower) ^ count)
    (fun lift same scratch fresh =>
      (original.currentInput lift same).finalizedInnerBody (services := services)
        (original.currentSampler lift same scratch fresh) (currentCheckers lift) count)
    environment (fun lift same scratch fresh =>
      original.fresh_finalized_loop_bound lift same scratch fresh environment
        basePoint targetPoint count lower atMostOne
        (prepared lift same scratch fresh) (quality lift same scratch fresh))

private def retainedFinalizedAttempts : Circuit
    (.quantum AlgorithmGate.model .empty BitWord.model services) ctx (persistentCtx ctx 256 260) :=
  (retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    ctx 256 260).seq (original.scopedAttemptsFinalized (services := services) 3)

private def FinalizedPackedFailure : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    ((original.runFinalized (services := services)).code.execute
      environment Reference state).effectWeight
        (fun entry => if entry.1.read (batchResultRead ctx 256 260) = .optionNone then
          Effect.one ((batchResultCtx ctx 256 260).register.prod Reference)
        else Effect.zero ((batchResultCtx ctx 256 260).register.prod Reference)) =
      CheckerTail.readWeight
        ((original.retainedFinalizedAttempts (services := services)).execute
          environment Reference state)
        (fun store => (store.read (.storage (Checkers.retained ctx).accepted.toCStorageRef)).toBool)
        false

/-- The finalized run's absent option has exactly its accepted-false flag weight. -/
lemma storage_runFinalized_none_weight : original.FinalizedPackedFailure environment := by
  unfold FinalizedPackedFailure
  intro Reference History _ state
  exact packed_none_weight_after 256 260
    (original.retainedFinalizedAttempts (services := services)) environment state

private def FinalizedRunFailureBound (basePoint targetPoint : Pure.Point original.curve)
    (lower : ℝ) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    Conditional.inputsSupported original (Transport.id ctx) basePoint targetPoint state →
    ((original.runFinalized (services := services)).code.execute
      environment Reference state).effectWeight
        (fun entry => if entry.1.read (batchResultRead ctx 256 260) = .optionNone then
          Effect.one ((batchResultCtx ctx 256 260).register.prod Reference)
        else Effect.zero ((batchResultCtx ctx 256 260).register.prod Reference)) ≤
      (1 - lower) ^ 3 * state.mass

/-- Actual three-attempt finalized output failure, conditional on the same internal evidence. -/
lemma runFinalized_failure_le_of_internal_evidence
    (basePoint targetPoint : Pure.Point original.curve) (lower : ℝ) (atMostOne : lower ≤ 1)
    (prepared : original.InternalPreparation environment basePoint targetPoint)
    (quality : original.InternalCandidateMass environment basePoint targetPoint lower) :
    original.FinalizedRunFailureBound environment basePoint targetPoint lower := by
  intro Reference History _ state supported
  have packed := original.storage_runFinalized_none_weight environment state
  have sequential := stored_weight_seq
    (retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx 256 260) (original.scopedAttemptsFinalized (services := services) 3) environment state
    (fun store => flagEffect ((persistentCtx ctx 256 260).register.prod Reference)
      (flagInputRead (.storage (Checkers.retained ctx).accepted.toCStorageRef) store) false)
  have scopeBound := original.scopedAttemptsFinalized_failure_le_of_internal_evidence
    environment basePoint targetPoint 3 lower atMostOne prepared quality
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
