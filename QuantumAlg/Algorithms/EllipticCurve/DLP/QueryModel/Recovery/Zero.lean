/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Failure
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Boundary
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Prefix
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol

/-!
# Zero actual rounds return the paid packed absent result with probability one
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local instance] Classical.decEq Classical.propDecidable

private theorem allocatedEmpty_none_weight {model : ExecutionModel} [BitWord.Selected model]
    {origin ctx : RuntimeCtx model.kind} (setup : Circuit model origin ctx)
    (width scalar : Nat) {Reference : Register} {History : Type} [Fintype History]
    (initial : State origin Reference (model.HiddenState × History)) :
    ((setup.seq
      (((retainPersistent (model := model) ctx width scalar).seq
        (Circuit.id (persistentCtx ctx width scalar))).seq
          (packBatchResult (model := model) ctx width scalar))).execute
      Reference initial).effectWeight
      (fun record => if record.1.read (batchResultRead ctx width scalar) = .optionNone then
        Effect.one ((batchResultCtx ctx width scalar).register.prod Reference)
      else Effect.zero ((batchResultCtx ctx width scalar).register.prod Reference)) =
        initial.mass := by
  let allocate := retainPersistent (model := model) ctx width scalar
  let empty := Circuit.id (model := model) (persistentCtx ctx width scalar)
  let pack := packBatchResult (model := model) ctx width scalar
  have completed := Circuit.storedWeight_four_stage setup allocate empty pack initial
    (fun store => if store.read (batchResultRead ctx width scalar) = .optionNone then
      Effect.one ((batchResultCtx ctx width scalar).register.prod Reference)
    else Effect.zero ((batchResultCtx ctx width scalar).register.prod Reference))
  have packed := packBatchResult_none_weight (model := model) width scalar
    (((setup.seq allocate).seq empty).execute Reference initial)
  have erased : persistentFailureWeight (model := model) (ctx := ctx) (width := width)
      (scalarWidth := scalar) (((setup.seq allocate).seq empty).execute Reference initial) =
    persistentFailureWeight (model := model) (ctx := ctx) (width := width) (scalarWidth := scalar)
      ((setup.seq allocate).execute Reference initial) := by
    unfold persistentFailureWeight
    rw [Circuit.execute_seq, State.effectWeight_mapHistory]
    rw [Circuit.execute_id_mapClassical, ExecutionState.effectWeight_mapClassical_decision]
  exact completed.trans (packed.trans (erased.trans
    (initializedFailureWeight setup width scalar initial)))

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Zero requested rounds still allocate and pack the real absent result with probability one. -/
public theorem ecdlpRecovery_zero_run_none_probability (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles
      (Sampling.pre I) Reference) :
    (run I A expansion nontrivial 0).outputDistribution original .optionNone = 1 := by
  let initial := original.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have complete := allocatedEmpty_none_weight (Sampling.Reuse.initialCode I A)
    (fieldWidth E) (scalarWidth I) initial
  rw [ExecutionState.mapClassical_mass, original.normalized] at complete
  rw [AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  exact (congrArg ENNReal.ofReal complete).trans ENNReal.ofReal_one

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
