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
# Complete actual finite-retry contracts at arbitrary natural batch counts

The sole algorithm run executes the public-modulus input. The original
good-key model appears only in the independent accepted-factor predicate
and success proof. Every contract carries the complete output-state target,
separate mandatory borrowed restoration, and independent native event,
resident, auxiliary and depth formulas for that same actual finite run.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

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
public def fixedRoundProblem (N : Nat) (totalRounds : Nat) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model) base
      (context base noQuantum N totalRounds)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  Witness := GoodKeyModel N
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ model _ output => NativeRetrySelection.decodeFactor output ∈
    NativeBatchSuccess.accepts model
  successLB := fun _ model =>
    ⟨1 - Calibration.batchFailure model.bitWidth ^ totalRounds, tsub_le_self⟩
  states := fun _ _ => [stateRequirement base noQuantum N totalRounds]
  resources :=
    { events := eventEnvelope N totalRounds
      resident := base.residentSpace + additionalSpace N totalRounds
      auxiliary := base.auxiliarySpace + additionalSpace N totalRounds }
  quantumTimeLimit := depthBound N totalRounds

private lemma accepts_probability (model : GoodKeyModel N) (totalRounds : Nat)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    ((run base noQuantum model.input totalRounds).outputDistribution environment
      input).toOuterMeasure
        {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts model} =
      ((run base noQuantum model.input totalRounds).outputDistribution environment
        input).toOuterMeasure
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
      have sound := run_some_sound (environment := environment)
        base noQuantum model.input totalRounds input word supported
      have declared := model.semiprime.nontrivial_factor_eq_declared
        sound.1 sound.2.1 sound.2.2
      exact iff_of_true ((NativeBatchSuccess.accepts_some model).mpr declared)
        (by intro impossible; cases impossible)

private lemma relational_probability (model : GoodKeyModel N) (totalRounds : Nat)
    {Reference : Register}
    (input : Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    ((algorithm base noQuantum model.input totalRounds).relationalDistribution environment
      input).toOuterMeasure
        {pair | (fixedRoundProblem base noQuantum N totalRounds).accepts environment model pair.1
          pair.2} =
      ((run base noQuantum model.input totalRounds).outputDistribution environment
        input).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
  have projection :
      ((algorithm base noQuantum model.input totalRounds).relationalDistribution environment
        input).toOuterMeasure
          {pair | (fixedRoundProblem base noQuantum N totalRounds).accepts environment model
            pair.1 pair.2} =
        ((run base noQuantum model.input totalRounds).outputDistribution environment
          input).toOuterMeasure
          {output | NativeRetrySelection.decodeFactor output ∈
            NativeBatchSuccess.accepts model} := by
    simp only [Algorithm.relationalDistribution, algorithm, AlgorithmRun.relationalDistribution,
      AlgorithmRun.outputDistribution, PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.trans (accepts_probability base noQuantum model totalRounds input)

/-- One actual algorithm meets every independent finite-count probability,
state and resource gate. -/
lemma algorithm_solves_fixedRound (specification : Input N) (totalRounds : Nat) :
    Algorithm.Solves (algorithm base noQuantum specification totalRounds)
      (fixedRoundProblem base noQuantum N totalRounds) := by
  constructor
  · intro environment model Reference input _valid _initialized
    rw [relational_probability (environment := environment)
      base noQuantum model totalRounds input]
    exact run_successProbability_ge base noQuantum model totalRounds input
  · intro environment model Reference input _valid _initialized requirement present
    have same : requirement = stateRequirement base noQuantum N totalRounds :=
      List.mem_singleton.mp present
    subst requirement
    exact stateRequirement_holds base noQuantum N specification totalRounds input
  · intro environment model Reference input _valid _initialized
    exact run_restoresBorrowed base noQuantum specification totalRounds input
  · intro _environment _model _Reference _input _valid _initialized path _supported
    exact run_pool_le base noQuantum specification totalRounds path
  · intro _environment _model _Reference _input _valid _initialized path _supported
    exact run_resident_le base noQuantum specification totalRounds path
  · intro _environment _model _Reference _input _valid _initialized path _supported
    exact run_auxiliary_le base noQuantum specification totalRounds path
  · intro _environment _model _Reference _input _valid _initialized path _supported
    exact run_quantumTime_le base noQuantum specification totalRounds path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
