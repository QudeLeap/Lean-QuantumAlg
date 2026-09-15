/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Soundness

/-!
# Exact probability and factor safety for every finite total batch count

The zero-round actual run retains its empty result, and each positive-round
run uses the existing chronological selection law. Together they give the
original first-success distribution for every natural total count. Natural
factor decoding remains a mathematical observation of the actual typed word.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

noncomputable section

open Execution ClassicalRoutines.FirstAccepted.Direct

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every natural total count has the original chronological first-success distribution. -/
theorem run_outputDistribution (specification : Input N) (totalRounds : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    (run base noQuantum specification totalRounds).outputDistribution input =
      Optional.Distribution.selectedDistribution
        ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue)
        totalRounds := by
  cases totalRounds with
  | zero =>
      change (NativeRetryEmpty.run base N).outputDistribution input = _
      rw [NativeRetryEmpty.run_outputDistribution]
      simp only [Optional.Distribution.selectedDistribution, PMF.independentReplicateVector,
        PMF.pure_map, Optional.Distribution.firstValue, List.Vector.toList_nil, List.foldl_nil]
  | succ count =>
      exact NativeRetrySelection.run_selectedDistribution base noQuantum specification count input

/-- Actual empty-output probability is the original batch failure probability to the total count. -/
theorem run_none (specification : Input N) (totalRounds : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    (run base noQuantum specification totalRounds).outputDistribution input
        CShape.Value.optionNone =
      sampledBatchOutputPMF specification none ^ totalRounds := by
  rw [run_outputDistribution, Optional.Distribution.selectedDistribution_none,
    NativeRetrySelection.batch_outputValue_none]

/-- The actual populated-output event has the exact complementary finite success probability. -/
theorem run_successProbability (specification : Input N) (totalRounds : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((run base noQuantum specification totalRounds).outputDistribution input).toOuterMeasure
        {value | value ≠ CShape.Value.optionNone} =
      1 - sampledBatchOutputPMF specification none ^ totalRounds := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  have complement : {value : (LatticeBatchRecoveryOutput.OutputShape N).Value |
      ¬ value ≠ CShape.Value.optionNone} = {CShape.Value.optionNone} := by
    ext value
    simp only [not_not, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [complement, PMF.toOuterMeasure_apply_singleton, run_none]

/-- Mathematical natural decoding preserves the actual empty-output event for every total count. -/
theorem run_decoded_none (specification : Input N) (totalRounds : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((run base noQuantum specification totalRounds).outputDistribution input).map
        NativeRetrySelection.decodeFactor none =
      sampledBatchOutputPMF specification none ^ totalRounds := by
  cases totalRounds with
  | zero =>
      change ((NativeRetryEmpty.run base N).outputDistribution input).map
        NativeRetrySelection.decodeFactor none = _
      rw [NativeRetryEmpty.run_outputDistribution, PMF.pure_map]
      change (PMF.pure (none : Option Nat)) none = _
      simp only [PMF.pure_apply, if_true, pow_zero]
  | succ count =>
      exact NativeRetrySelection.run_decoded_none base noQuantum specification count input

/-- Every supported populated actual word decodes to a nontrivial divisor of the modulus. -/
theorem run_some_sound (specification : Input N) (totalRounds : Nat)
    {Reference : Register} (input : Execution.Input base Reference)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((run base noQuantum specification totalRounds).outputDistribution input).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [run_outputDistribution] at supported
  exact NativeRetrySelection.batch_outputValue_some_sound specification word
    (Optional.Distribution.selectedDistribution_some_support _ totalRounds word supported)

/-- Every supported populated natural observation is the same checked nontrivial divisor. -/
theorem run_decoded_some_sound (specification : Input N) (totalRounds : Nat)
    {Reference : Register} (input : Execution.Input base Reference) (factor : Nat)
    (supported : some factor ∈
      (((run base noQuantum specification totalRounds).outputDistribution input).map
        NativeRetrySelection.decodeFactor).support) :
    factor ∣ N ∧ 1 < factor ∧ factor < N := by
  rw [PMF.mem_support_map_iff] at supported
  rcases supported with ⟨value, member, decoded⟩
  cases value with
  | optionNone => cases decoded
  | optionSome word =>
      have valueEq : word.toNat = factor := Option.some.inj decoded
      exact valueEq ▸ run_some_sound base noQuantum specification totalRounds input word member

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
