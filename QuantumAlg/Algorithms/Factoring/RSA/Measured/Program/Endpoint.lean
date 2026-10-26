/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Success
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.State
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Borrowed
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Events
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.QuantumTime
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Complete independent contracts for the actual measured constant-workspace RSA parent

The sole actual run supplies original finite-retry success, every complete
output/reference state, borrowed restoration and native event/space/time
bounds. Width and oddness follow internally from the original ordered-key
witness; neither the runtime domain nor the original key domain is restricted
[EH17, source.tex:878-966; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]
variable {environment : MeasuredRSAModel.Environment}

open Execution EkeraHastadStyle.Canonical
open ClassicalRoutines.FirstAccepted.Direct

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

omit configuration in
private lemma keyArithmeticWidth (key : GoodKeyModel N) : 5 ≤ arithmeticBits N := by
  rw [key.modulus_eq]
  exact measuredRSA_orderedKey_arithmeticWidth key.pair

omit configuration in
private lemma keyOdd (key : GoodKeyModel N) : Odd N := by
  rw [key.modulus_eq]
  exact measuredRSA_orderedKey_odd key.pair

/-- The sole execution source is the actual single-control chronological parent. -/
def algorithm (input : Input N) (count : Nat) :
    Algorithm MeasuredRSAModel base
      (outputContext base noQuantum N count) (LatticeBatchRecoveryOutput.OutputShape N) where
  run := run base noQuantum N input count

/-- Complete independent finite-count problem for the new physical execution. -/
def fixedRoundProblem (N count : Nat) :
    Problem MeasuredRSAModel base
      (outputContext base noQuantum N count) (LatticeBatchRecoveryOutput.OutputShape N) where
  Witness := GoodKeyModel N
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ key _ output => NativeRetrySelection.decodeFactor output ∈
    NativeBatchSuccess.accepts key
  successLB := fun _ key => ⟨1 - NativeFiniteRetry.Calibration.batchFailure key.bitWidth ^ count,
    tsub_le_self⟩
  states := fun _ _ => [stateRequirement base noQuantum N count]
  resources :=
    { events := eventBudget N count
      resident := base.residentSpace + spaceLimit N count
      auxiliary := base.auxiliarySpace + spaceLimit N count }
  quantumTimeLimit := quantumTimeLimit N count

private lemma accepts_probability (specification : Input N) (key : GoodKeyModel N) (count : Nat)
    {Reference : Register}
    (input : OracleInput MeasuredRSAModel.classicalOracles base Reference) :
    ((run base noQuantum N specification count).outputDistribution environment input).toOuterMeasure
        {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts key} =
      ((run base noQuantum N specification count).outputDistribution environment
        input).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
  apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
  ext output
  simp only [Set.mem_inter_iff]
  apply and_congr_left
  intro supported
  cases output with
  | optionNone =>
      change none ∈ NativeBatchSuccess.accepts key ↔
        (CShape.Value.optionNone : (LatticeBatchRecoveryOutput.OutputShape N).Value) ≠ .optionNone
      simp only [NativeBatchSuccess.not_accepts_none, ne_eq, not_true_eq_false]
  | optionSome word =>
      have sound := rsaMeasuredParent_run_some_sound base noQuantum specification count
        input word supported
      have declared := key.semiprime.nontrivial_factor_eq_declared sound.1 sound.2.1 sound.2.2
      exact iff_of_true ((NativeBatchSuccess.accepts_some key).mpr declared)
        (by intro impossible; cases impossible)

/-- Relational acceptance observes the same original input and the actual stored factor. -/
lemma rsaMeasuredParent_relational_probability
    (specification : Input N) (key : GoodKeyModel N) (count : Nat)
    {Reference : Register}
    (input : OracleInput MeasuredRSAModel.classicalOracles base Reference) :
    ((algorithm base noQuantum specification count).relationalDistribution environment
      input).toOuterMeasure
        {pair | (fixedRoundProblem base noQuantum N count).accepts environment key pair.1 pair.2} =
      ((run base noQuantum N specification count).outputDistribution environment
        input).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
  have projection :
      ((algorithm base noQuantum specification count).relationalDistribution environment
        input).toOuterMeasure
          {pair | (fixedRoundProblem base noQuantum N count).accepts environment key pair.1
            pair.2} =
        ((run base noQuantum N specification count).outputDistribution environment
          input).toOuterMeasure
          {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts key} := by
    simp only [Algorithm.relationalDistribution, algorithm, AlgorithmRun.relationalDistribution,
      AlgorithmRun.outputDistribution, PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.trans (accepts_probability base noQuantum specification key count input)

/-- One actual algorithm meets all seven gates with independent budgets and no kernel premise. -/
lemma rsaMeasuredParent_algorithm_solves_fixedRound (specification : Input N) (count : Nat) :
    (algorithm base noQuantum specification count).Solves
      (fixedRoundProblem base noQuantum N count) := by
  constructor
  · intro environment key Reference input _valid _initialized
    rw [rsaMeasuredParent_relational_probability (environment := environment)
      base noQuantum specification key count input]
    exact rsaMeasuredParent_run_successProbability_ge base noQuantum specification key count input
  · intro environment key Reference input _valid _initialized requirement present
    have same : requirement = stateRequirement base noQuantum N count :=
      List.mem_singleton.mp present
    subst requirement
    exact rsaMeasuredParent_stateRequirement_holds base noQuantum N specification count input
  · intro environment key Reference input _valid _initialized
    exact rsaMeasuredParent_restoresBorrowed base noQuantum N specification count input
  · intro _environment key _Reference _input _valid _initialized path _supported
    exact rsaMeasuredParent_run_pool_le base noQuantum N specification
      (keyArithmeticWidth key) (keyOdd key) count path
  · intro _environment _key _Reference _input _valid _initialized path _supported
    exact rsaMeasuredParent_run_resident_le base noQuantum N specification count path
  · intro _environment _key _Reference _input _valid _initialized path _supported
    exact rsaMeasuredParent_run_auxiliary_le base noQuantum N specification count path
  · intro _environment key _Reference _input _valid _initialized path _supported
    exact rsaMeasuredParent_run_quantumTime_le base noQuantum specification
      (keyArithmeticWidth key) (keyOdd key) count path

end

end QuantumAlg.Factoring.RSA.Measured.Program
