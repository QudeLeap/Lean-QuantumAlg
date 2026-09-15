/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

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

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The executable input supplies only the original modulus data and exact total batch count. -/
def algorithm (specification : Input N) (totalRounds : Nat) :
    Algorithm .quantum base (context base noQuantum N totalRounds)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  run := run base noQuantum specification totalRounds

/-- The independent finite-count problem accepts exactly the two original declared factors.

Every normalized classical input and external-reference extension is admitted.
Preparation, stored measurements, complete recovery and ordered selection are
internal to the actual run. Its complete joint state requirement includes every
live quantum wire and the full reference, even on failure. Native event and
space bounds include actual outcome storage, retained outputs and reused work;
unit-event depth is an independent serial bound. Zero batches are included.
-/
def fixedRoundProblem (model : GoodKeyModel N) (totalRounds : Nat) :
    Problem .quantum base (context base noQuantum N totalRounds)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := fun _ => True
  accepts := fun _ output => NativeRetrySelection.decodeFactor output ∈
    NativeBatchSuccess.accepts model
  successLB := ⟨1 - Calibration.batchFailure model.bitWidth ^ totalRounds, tsub_le_self⟩
  states := [stateRequirement base noQuantum N totalRounds]
  resources :=
    { events := eventEnvelope N totalRounds
      resident := base.residentSpace + additionalSpace N totalRounds
      auxiliary := base.auxiliarySpace + additionalSpace N totalRounds }
  depth := .quantum (fun _ => 1) (depthBound N totalRounds)

private theorem accepts_probability (model : GoodKeyModel N) (totalRounds : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
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
    {Reference : Register} (input : Execution.Input base Reference) :
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
  · intro Reference input _valid
    rw [relational_probability]
    exact run_successProbability_ge base noQuantum model totalRounds input
  · intro Reference input _valid requirement present
    have same : requirement = stateRequirement base noQuantum N totalRounds :=
      List.mem_singleton.mp present
    subst requirement
    exact stateRequirement_holds base noQuantum N model.input totalRounds input
  · intro Reference input _valid
    exact run_restoresBorrowed base noQuantum model.input totalRounds input
  · intro _Reference _input _valid path _supported
    exact run_pool_le base noQuantum model.input totalRounds path
  · intro _Reference _input _valid path _supported
    exact run_resident_le base noQuantum model.input totalRounds path
  · intro _Reference _input _valid path _supported
    exact run_auxiliary_le base noQuantum model.input totalRounds path
  · intro _Reference _input _valid path _supported
    exact run_depth_le base noQuantum model.input totalRounds path

/-- The original rational target reserves half its failure mass for the independent key exception.
Every state and resource obligation is the same finite-count independent contract. -/
def problem (model : GoodKeyModel N) (budget : FailureBudget) :
    Problem .quantum base (context base noQuantum N (Calibration.retryCount budget))
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
  intro Reference input _valid
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
