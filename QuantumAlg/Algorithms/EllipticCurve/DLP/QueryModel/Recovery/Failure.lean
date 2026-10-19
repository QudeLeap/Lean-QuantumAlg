/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.SuccessFloor
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Probability
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Support
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.SuccessFloor
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Loop
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Boundary
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Prefix

/-!
# Actual finite declared-query ECDLP failure probability

The same admitted original input determines every real reset, sample,
complete checked attempt and first-success update. Its actual unnormalized
failure mass contracts along those prefixes. The one final option pack
reads exactly that remaining mass. All finite counts, quantum references
and existing history correlations are retained without an independence
assumption or a caller-supplied probability certificate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local instance] Classical.decEq
attribute [local irreducible] sampleUnderPersistent retainPersistent

private lemma initializedFailureWeight {model : ExecutionModel}
    {environment : model.Environment}
    {origin ctx : RuntimeCtx model.kind} (setup : Circuit model origin ctx)
    (width scalar : Nat) {Reference : Register} {History : Type} [Fintype History]
    (initial : State origin Reference (model.HiddenState × History)) :
    persistentFailureWeight (model := model) (ctx := ctx) (width := width) (scalarWidth := scalar)
      ((setup.seq (retainPersistent ctx width scalar)).execute environment Reference initial) =
        initial.mass := by
  exact (storedWeight_seq setup (retainPersistent ctx width scalar) initial (fun store =>
    if (store.read (.storage (persistentAccepted ctx width scalar).toCStorageRef)).toBool = false
      then Effect.one ((persistentCtx ctx width scalar).register.prod Reference)
    else Effect.zero ((persistentCtx ctx width scalar).register.prod Reference))).trans
      ((retainPersistent_failure_weight width scalar (setup.execute environment Reference
        initial)).trans
        (setup.execute_mass environment Reference initial))

attribute [local instance] Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original input domain fixes both public points and permits every reference extension. -/
public def inputDomain (I : ECDLPInstance E)
    (state : ExecutionState (Store (Sampling.pre I)) (Sampling.pre I).register) : Prop :=
  ∀ store, 0 < (state.block store).mass → store = Runtime.Context.inputStore I

private lemma successFloor_le_one (I : ECDLPInstance E) : Sampling.Reuse.successFloor I ≤ 1 := by
  change FiniteCyclicDLP.Canonical.attemptFloor (problem I) ≤ 1
  unfold FiniteCyclicDLP.Canonical.attemptFloor
  have positive : 0 < (FiniteCyclicDLP.Canonical.successDenominator (problem I) : ℝ) := by
    unfold FiniteCyclicDLP.Canonical.successDenominator FiniteCyclicDLP.fourierModulus
    positivity
  apply (div_le_one positive).mpr
  exact_mod_cast (FiniteCyclicDLP.Canonical.successNumerator_lt_successDenominator (problem I)).le

private lemma indicator_decision_weight {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (condition : C → Prop)
    (first second : DecidablePred condition) :
    state.effectWeight (fun entry => @ite (Effect R) (condition entry) (first entry)
      (Effect.one R) (Effect.zero R)) =
      state.effectWeight (fun entry => @ite (Effect R) (condition entry) (second entry)
        (Effect.one R) (Effect.zero R)) := by
  cases Subsingleton.elim first second
  rfl

variable [Fact p.Prime]

private lemma code_none_weight_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (secretInput : FiniteCyclicDLP.Canonical.Probability.SecretInput (problem I))
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State (Sampling.pre I) Reference
      ((Sampling.executionModel I).HiddenState × History))
    (admitted : ∀ entry, 0 < (initial.block entry).mass → entry.1 = Runtime.Context.inputStore I) :
    ((code I expansion nontrivial count).execute (Sampling.sourceEnvironment I A) Reference
      initial).effectWeight
      (fun record => if record.1.read
        (batchResultRead (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)) = .optionNone
          then
          Effect.one ((post I).register.prod Reference)
        else Effect.zero ((post I).register.prod Reference)) ≤
      (1 - Sampling.Reuse.successFloor I) ^ count * initial.mass := by
  let ctx := Sampling.Reuse.context I
  let width := fieldWidth E
  let scalar := scalarWidth I
  let setup := Sampling.Reuse.initialCode I
  let allocation : Circuit (Sampling.executionModel I) ctx (persistentCtx ctx width scalar) :=
    retainPersistent (model := Sampling.executionModel I) ctx width scalar
  let body := sampledAttempts (Sampling.Reuse.code (allowAllocation := false) I expansion)
    count (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
  let packing : Circuit (Sampling.executionModel I)
      (persistentCtx ctx width scalar) (batchResultCtx ctx width scalar) :=
    packBatchResult (model := Sampling.executionModel I) ctx width scalar
  have geometric := sampledAttempts_failure_weight_le_on_prefix (environment :=
    Sampling.sourceEnvironment I A)
    (Sampling.Reuse.code (allowAllocation := false) I expansion)
    count (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
    I.basePoint.toMathlib I.targetPoint.toMathlib initial
    (fun priorCode => ecdlpRecovery_prefix_represents I A initial admitted priorCode)
    (Sampling.Reuse.successFloor I) (successFloor_le_one I)
    (fun K _ state =>
      (ecdlpRecovery_sample_weight_bound I A expansion nontrivial secretInput state).trans_eq
        (indicator_decision_weight _ _ _ _)) (setup.seq allocation)
  have initialized : persistentFailureWeight (model := Sampling.executionModel I)
      (ctx := ctx) (width := width) (scalarWidth := scalar)
      ((setup.seq allocation).execute (Sampling.sourceEnvironment I A) Reference initial) =
        initial.mass := by
    exact initializedFailureWeight setup width scalar initial
  rw [initialized] at geometric
  have completed := Circuit.storedWeight_four_stage setup allocation body packing
    (Sampling.sourceEnvironment I A) initial
    (fun store => if store.read (batchResultRead ctx width scalar) = .optionNone then
      Effect.one ((batchResultCtx ctx width scalar).register.prod Reference)
    else Effect.zero ((batchResultCtx ctx width scalar).register.prod Reference))
  have packed := packBatchResult_none_weight (environment := Sampling.sourceEnvironment I A)
    width scalar
    (((setup.seq allocation).seq body).execute (Sampling.sourceEnvironment I A) Reference initial)
  exact (completed.trans packed).trans_le geometric

/-- The actual complete finite run's absent output obeys the original geometric failure bound. -/
public lemma ecdlpRecovery_run_none_probability_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (secretInput : FiniteCyclicDLP.Canonical.Probability.SecretInput (problem I))
    {Reference : Register}
    (original : OracleInput (Sampling.executionModel I).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState) :
    (run I expansion nontrivial count).outputDistribution (Sampling.sourceEnvironment I A)
      original .optionNone ≤
      ENNReal.ofReal ((1 - Sampling.Reuse.successFloor I) ^ count) := by
  let initial := original.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have admitted : ∀ entry, 0 < (initial.block entry).mass →
      entry.1 = Runtime.Context.inputStore I := by
    intro entry positive
    obtain ⟨source, same, present⟩ := (ExecutionState.mapClassical_block_mass_pos_iff original.state
      (fun value => (value.1, (value.2, value.1))) entry).mp positive
    have expected := valid source.1 (original.caller_local_mass_pos_of_joint source present)
    exact (congrArg Prod.fst same).symm.trans expected
  have failure := code_none_weight_le I A expansion nontrivial count secretInput initial admitted
  rw [ExecutionState.mapClassical_mass, original.normalized, mul_one] at failure
  rw [AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  exact ENNReal.ofReal_le_ofReal failure

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
