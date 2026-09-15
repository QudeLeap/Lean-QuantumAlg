/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite.Correctness
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# One actual original-width oracle run meets its independent problem

The original finite retry supplies the only execution, output and probability
law. All normalized input states and reference extensions are admitted. Complete
borrowed restoration follows the actual interpreter with no borrowed quantum
wire; classical-reference correlations are preserved jointly. No final zero-bank
promise is substituted for the actual post-measurement state.

The independent native pool and arbitrary-duration critical-path allowance
include every charged reset and both real sample packs. Original good-key data
enter only the accepted-factor relation and the numerical success theorem.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The finite named candidate uses exactly the existing actual complete run at its total count. -/
public def finiteAlgorithm (specification : Input N) (count : Nat) :
    Algorithm .quantum base (outputContext base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  run := Retry.Finite.run base noQuantum N specification count

/-- The calibrated candidate passes only the public modulus data and the original retry count. -/
public def algorithm (specification : Input N) (budget : FailureBudget) :
    Algorithm .quantum base (outputContext base noQuantum N (calibratedCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  finiteAlgorithm base noQuantum specification (calibratedCount budget)

private theorem accepts_probability (model : GoodKeyModel N) (count : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((Retry.Finite.run base noQuantum N model.input count).outputDistribution
        input).toOuterMeasure
        {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts model} =
      ((Retry.Finite.run base noQuantum N model.input count).outputDistribution
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
      have sound := Retry.Finite.nativeOracle_finiteRetry_some_sound
        base noQuantum N model.input count input word supported
      have declared := model.semiprime.nontrivial_factor_eq_declared
        sound.1 sound.2.1 sound.2.2
      exact iff_of_true ((NativeBatchSuccess.accepts_some model).mpr declared)
        (by intro impossible; cases impossible)

private theorem relational_probability (model : GoodKeyModel N) (count : Nat)
    (duration : Resource.Event .quantum → Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((finiteAlgorithm base noQuantum model.input count).relationalDistribution input).toOuterMeasure
        {pair | (finiteProblem base noQuantum model count duration).accepts pair.1 pair.2} =
      ((Retry.Finite.run base noQuantum N model.input count).outputDistribution
        input).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
  have projection :
      ((finiteAlgorithm base noQuantum model.input count).relationalDistribution
        input).toOuterMeasure
          {pair | (finiteProblem base noQuantum model count duration).accepts pair.1 pair.2} =
        ((Retry.Finite.run base noQuantum N model.input count).outputDistribution
          input).toOuterMeasure
            {output | NativeRetrySelection.decodeFactor output ∈
              NativeBatchSuccess.accepts model} := by
    simp only [Algorithm.relationalDistribution, finiteAlgorithm,
      AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.trans (accepts_probability base noQuantum model count input)

/-- The same finite execution restores every borrowed classical-reference correlation jointly. -/
theorem nativeOracle_finiteAlgorithm_restoresBorrowed (specification : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    (finiteAlgorithm base noQuantum specification count).run.RestoresBorrowed input := by
  have empty : base.borrowedQuantumWires = [] := by
    have subset := base.borrowedQuantumWires_sublist
    rw [noQuantum] at subset
    exact List.sublist_nil.mp subset
  exact Circuit.borrowedRestored_of_noBorrowedQuantum _ empty Reference
    (input.state.mapClassical (fun store => (store, store)))

/-- Every original caller entry and every actually retained cell and wire occurs in the output. -/
theorem nativeOracle_finiteAlgorithm_output_listing (specification : Input N) (count : Nat) :
    (finiteAlgorithm base noQuantum specification count).run.output.listing =
      (outputContext base noQuantum N count).keys :=
  Retry.Finite.nativeOracle_finiteRetry_output_listing base noQuantum N specification count

/-- One actual finite execution meets the independent success, restoration and resource contract. -/
theorem nativeOracle_finiteAlgorithm_solves (model : GoodKeyModel N) (count : Nat)
    (duration : Resource.Event .quantum → Nat) :
    Algorithm.Solves (finiteAlgorithm base noQuantum model.input count)
      (finiteProblem base noQuantum model count duration) := by
  constructor
  · intro Reference input _valid
    rw [relational_probability]
    exact Retry.Finite.nativeOracle_finiteRetry_successProbability_ge
      base noQuantum N model count input
  · intro _Reference _input _valid _requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _valid
    exact nativeOracle_finiteAlgorithm_restoresBorrowed base noQuantum model.input count input
  · intro _Reference _input _valid path _supported
    have bounds := Retry.Finite.nativeOracle_finiteRetry_resourcePool_le
      base noQuantum N model.input count
    rw [← Retry.Finite.nativeOracle_finiteRetry_run_code base noQuantum N model.input count]
      at bounds
    exact bounds path
  · intro _Reference _input _valid path _supported
    have bounds := Retry.Finite.nativeOracle_finiteRetry_peakResidentSpace_le
      base noQuantum N model.input count
    rw [← Retry.Finite.nativeOracle_finiteRetry_run_code base noQuantum N model.input count]
      at bounds
    exact bounds path
  · intro _Reference _input _valid path _supported
    have bounds := Retry.Finite.nativeOracle_finiteRetry_peakAuxiliarySpace_le
      base noQuantum N model.input count
    rw [← Retry.Finite.nativeOracle_finiteRetry_run_code base noQuantum N model.input count]
      at bounds
    exact bounds path
  · intro _Reference _input _valid path _supported
    have bounds := Retry.Finite.nativeOracle_finiteRetry_depth_le
      base noQuantum N model.input count duration
    rw [← Retry.Finite.nativeOracle_finiteRetry_run_code base noQuantum N model.input count]
      at bounds
    exact bounds path

/-- Original rational calibration applies to the same actual independent native contract. -/
public theorem nativeOracle_algorithm_solves (model : GoodKeyModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    Algorithm.Solves (algorithm base noQuantum model.input budget)
      (problem base noQuantum model budget) := by
  refine { nativeOracle_finiteAlgorithm_solves base noQuantum model
    (calibratedCount budget) circuitDuration with success := ?_ }
  intro Reference input _valid
  change 1 - ENNReal.ofReal (budget.value / 2) ≤
    ((finiteAlgorithm base noQuantum model.input (calibratedCount budget)).relationalDistribution
      input).toOuterMeasure
        {pair | (finiteProblem base noQuantum model (calibratedCount budget)
          circuitDuration).accepts pair.1 pair.2}
  rw [relational_probability]
  exact (tsub_le_tsub_left
    (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget
      model.effective budget wellFormed) 1).trans
    (Retry.Finite.nativeOracle_finiteRetry_successProbability_ge
      base noQuantum N model (calibratedCount budget) input)

/-- The original-width oracle candidate solves the declared conditional factoring problem. -/
public theorem main (model : GoodKeyModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    Algorithm.Solves (algorithm base noQuantum model.input budget)
      (problem base noQuantum model budget) :=
  nativeOracle_algorithm_solves base noQuantum model budget wellFormed

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
