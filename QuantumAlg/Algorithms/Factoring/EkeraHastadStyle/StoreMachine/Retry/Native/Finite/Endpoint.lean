/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Resources
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.State
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Success
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.State
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Complete actual finite-retry contracts and rational-target calibration

The sole algorithm run executes the public-modulus input. The original
good-key model appears only in the independent accepted-factor predicate
and success proof. Every contract carries the complete output-state target,
separate mandatory borrowed restoration, and independent native event,
resident, auxiliary and depth formulas for that same actual finite run.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

noncomputable section

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The executable input supplies only the original modulus data and exact total batch count. -/
def algorithm (specification : Input N) (totalRounds : Nat) :
    Algorithm RuntimeRound.model base (context base noQuantum N totalRounds)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  run := run base noQuantum specification totalRounds

/-- Complete native factoring at an independently specified finite batch count.

**Input.** The public modulus comes from the original good-key model of two distinct
odd primes. Every normalized caller store and external-reference extension is admitted.
Preparation, parameter selection and measured execution are internal to the run.
**Output.** An optional factor word, accepted exactly when it contains one of the two
original primes. The independent state requirement specifies every final quantum wire
jointly with the reference, including failure; borrowed restoration is mandatory.
**Resource budget.** The independent event envelope, resident and auxiliary space
formulas include real native preparation, stored measurements, full classical recovery,
ordered selection and actual reuse of the single bank. Unit-event whole-run depth is
bounded by `depthBound N totalRounds`. Zero batches only allocate an empty result.
**Success.** At count k, the required probability is at least 1 - batchFailure^k,
using the original sampler-adjusted conditional batch floor and no added independence
hypothesis on the incoming caller state.
**Source.** [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:329-355]. The complete native
execution and independent finite-retry accounting are the implementation refinement.
-/
public def fixedRoundProblem (model : GoodKeyModel N) (totalRounds : Nat) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model) base
      (context base noQuantum N totalRounds)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ output => NativeRetrySelection.decodeFactor output ∈
    NativeBatchSuccess.accepts model
  successLB := ⟨1 - Calibration.batchFailure model.bitWidth ^ totalRounds, tsub_le_self⟩
  states := [stateRequirement base noQuantum N totalRounds]
  resources :=
    { events := eventEnvelope N totalRounds
      resident := base.residentSpace + additionalSpace N totalRounds
      auxiliary := base.auxiliarySpace + additionalSpace N totalRounds }
  depth :=
    { duration := fun _ => 1
      limit := depthBound N totalRounds
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

private theorem accepts_probability (model : GoodKeyModel N) (totalRounds : Nat)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    ((run base noQuantum model.input totalRounds).outputDistribution input).toOuterMeasure
        {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts model} =
      ((run base noQuantum model.input totalRounds).outputDistribution input).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
  apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
  ext output
  simp only [Set.mem_inter_iff]
  apply and_congr_left
  intro supported
  cases output with
  | optionNone =>
      change none ∈ NativeBatchSuccess.accepts model ↔
        (CShape.Value.optionNone : (LatticeBatchRecoveryOutput.OutputShape N).Value) ≠ .optionNone
      simp only [NativeBatchSuccess.not_accepts_none, ne_eq, not_true_eq_false]
  | optionSome word =>
      have sound := run_some_sound base noQuantum model.input totalRounds input word supported
      have declared := model.semiprime.nontrivial_factor_eq_declared
        sound.1 sound.2.1 sound.2.2
      exact iff_of_true ((NativeBatchSuccess.accepts_some model).mpr declared)
        (by intro impossible; cases impossible)

private theorem relational_probability (model : GoodKeyModel N) (totalRounds : Nat)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    ((algorithm base noQuantum model.input totalRounds).relationalDistribution input).toOuterMeasure
        {pair | (fixedRoundProblem base noQuantum model totalRounds).accepts pair.1 pair.2} =
      ((run base noQuantum model.input totalRounds).outputDistribution input).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
  have projection :
      ((algorithm base noQuantum model.input totalRounds).relationalDistribution
        input).toOuterMeasure
          {pair | (fixedRoundProblem base noQuantum model totalRounds).accepts pair.1 pair.2} =
        ((run base noQuantum model.input totalRounds).outputDistribution input).toOuterMeasure
          {output | NativeRetrySelection.decodeFactor output ∈
            NativeBatchSuccess.accepts model} := by
    simp only [Algorithm.relationalDistribution, algorithm, AlgorithmRun.relationalDistribution,
      AlgorithmRun.outputDistribution, PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.trans (accepts_probability base noQuantum model totalRounds input)

/-- One actual algorithm meets every independent finite-count probability,
state and resource gate. -/
theorem algorithm_solves_fixedRound (model : GoodKeyModel N) (totalRounds : Nat) :
    Algorithm.Solves (algorithm base noQuantum model.input totalRounds)
      (fixedRoundProblem base noQuantum model totalRounds) := by
  constructor
  · intro Reference input _valid _initialized
    rw [relational_probability]
    exact run_successProbability_ge base noQuantum model totalRounds input
  · intro Reference input _valid _initialized requirement present
    have same : requirement = stateRequirement base noQuantum N totalRounds :=
      List.mem_singleton.mp present
    subst requirement
    exact stateRequirement_holds base noQuantum N model.input totalRounds input
  · intro Reference input _valid _initialized
    exact run_restoresBorrowed base noQuantum model.input totalRounds input
  · intro _Reference _input _valid _initialized path _supported
    exact run_pool_le base noQuantum model.input totalRounds path
  · intro _Reference _input _valid _initialized path _supported
    exact run_resident_le base noQuantum model.input totalRounds path
  · intro _Reference _input _valid _initialized path _supported
    exact run_auxiliary_le base noQuantum model.input totalRounds path
  · intro _Reference _input _valid _initialized path _supported
    exact run_depth_le base noQuantum model.input totalRounds path

/-- Calibrated native factoring under the original good-key condition.

**Input.** The same good-key modulus and arbitrary normalized caller/reference state,
with the original rational failure budget.
**Output.** One of the two declared primes, with the same complete state and borrowed
restoration requirements as `fixedRoundProblem`.
**Resource budget.** The unchanged independent finite-count formulas at the original
`Calibration.retryCount budget`, including native quantum and full classical work.
**Success.** At least 1 - budget.value / 2 under the original well-formedness condition;
the other half of the failure target remains reserved for the separate key exception.
**Source.** The factoring reduction [EH17, source.tex:878-966] and lattice post-processing
[E23, arxiv-v5.tex:329-355], with the proved conditional batch floor and rational retry
calibration of `fixedRoundProblem`.
-/
public def problem (model : GoodKeyModel N) (budget : FailureBudget) :
    Problem RuntimeRound.model base (context base noQuantum N (Calibration.retryCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  { fixedRoundProblem base noQuantum model (Calibration.retryCount budget) with
    successLB := ⟨1 - ENNReal.ofReal (budget.value / 2), tsub_le_self⟩ }

/-- Original rational calibration applies to the same actual complete finite run. -/
theorem algorithm_solves (model : GoodKeyModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    Algorithm.Solves (algorithm base noQuantum model.input (Calibration.retryCount budget))
      (problem base noQuantum model budget) := by
  refine { algorithm_solves_fixedRound base noQuantum model (Calibration.retryCount budget) with
    success := ?_ }
  intro Reference input _valid _initialized
  change 1 - ENNReal.ofReal (budget.value / 2) ≤
    ((algorithm base noQuantum model.input (Calibration.retryCount budget)).relationalDistribution
      input).toOuterMeasure
        {pair | (fixedRoundProblem base noQuantum model (Calibration.retryCount budget)).accepts
          pair.1 pair.2}
  rw [relational_probability]
  exact run_successProbability_ge_halfTarget base noQuantum model budget wellFormed input

/-- A complete actual public-modulus execution meets the original calibrated good-key contract. -/
theorem main (model : GoodKeyModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    ∃ candidate, Algorithm.Solves candidate (problem base noQuantum model budget) :=
  ⟨algorithm base noQuantum model.input (Calibration.retryCount budget),
    algorithm_solves base noQuantum model budget wellFormed⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
