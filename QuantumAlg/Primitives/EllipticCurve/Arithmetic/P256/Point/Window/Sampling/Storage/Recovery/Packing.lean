/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.FailureLoop
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Boundary

/-!
# The actual fresh-feedback run's final optional result

The original option-pack instruction follows the real retained seven-cell
allocation and the actual three-attempt feedback scope. Its absent-output
weight is exactly that scope's returned accepted-false weight. This law
keeps every incoming Store, service state, History, Path and Reference;
it assumes neither a sampling floor nor a successful attempt.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma packed_none_weight_after {ctx before : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (width scalarWidth : Nat)
    (first : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      before (persistentCtx ctx width scalarWidth))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State before Reference (services.HiddenState × History)) :
    ((first.seq (packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx width scalarWidth)).execute
      environment Reference state).effectWeight
        (fun entry => if entry.1.read (batchResultRead ctx width scalarWidth) = .optionNone then
          Effect.one ((batchResultCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((batchResultCtx ctx width scalarWidth).register.prod Reference)) =
      CheckerTail.readWeight (first.execute environment Reference state)
        (fun store => (store.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool) false := by
  rw [Circuit.execute_seq, State.effectWeight_mapHistory]
  exact packBatchResult_none_weight
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (environment := environment) width scalarWidth
    (first.execute environment Reference state)

namespace Inputs

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private def retainedAttempts : Circuit
    (.quantum AlgorithmGate.model .empty BitWord.model services) ctx (persistentCtx ctx 256 260) :=
  (retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    ctx 256 260).seq (original.scopedAttempts (services := services) 3)

attribute [local irreducible] scopedAttempts

/-- The final output reads the original retained option cell after feedback release. -/
lemma storage_run_output_read (store : Store (batchResultCtx ctx 256 260)) :
    (original.run (services := services)).output.eval store =
      store.read (batchResultRead ctx 256 260) := rfl

private def PackedFailure : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    ((original.run (services := services)).code.execute environment Reference state).effectWeight
        (fun entry => if entry.1.read (batchResultRead ctx 256 260) = .optionNone then
          Effect.one ((batchResultCtx ctx 256 260).register.prod Reference)
        else Effect.zero ((batchResultCtx ctx 256 260).register.prod Reference)) =
      CheckerTail.readWeight
        ((original.retainedAttempts (services := services)).execute environment Reference state)
        (fun store => (store.read (.storage (Checkers.retained ctx).accepted.toCStorageRef)).toBool)
        false

/-- The same new run's missing-result mass equals its actual returned first-success flag mass. -/
lemma storage_run_none_weight : original.PackedFailure environment := by
  unfold PackedFailure
  intro Reference History _ state
  exact packed_none_weight_after 256 260 (original.retainedAttempts (services := services))
    environment state

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
