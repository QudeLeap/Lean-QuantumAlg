/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Recovery.Correctness
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Recovery.Failure
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Original ECDLP success on the actual complete repeated execution

The admitted local input fixes the two original public points and allows any
external reference extension. Positive actual output records contain only
failure or the original secret. The failure contraction on the real reused
bank therefore yields the original finite success bound, including zero
rounds. Its original retry calibration supplies the requested public budget.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution FiniteCyclicDLP.Concrete.Amplification

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem two_output_mass {Value : Type} [Finite Value]
    (distribution : PMF Value) (left right : Value) (distinct : left ≠ right)
    (zero : ∀ value, value ≠ left → value ≠ right → distribution value = 0) :
    distribution left + distribution right = 1 := by
  let := Fintype.ofFinite Value
  have restricted : (∑ value ∈ ({left, right} : Finset Value), distribution value) =
      ∑ value, distribution value := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro value _ excluded
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at excluded
    exact zero value excluded.1 excluded.2
  have total : (∑ value ∈ ({left, right} : Finset Value), distribution value) = 1 :=
    restricted.trans (by simpa only [tsum_fintype] using distribution.tsum_coe)
  simpa [distinct] using total

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem entered_valid (I : ECDLPInstance E) {Reference : Register}
    (original : Input (Runtime.Context.pre I) Reference)
    (valid : ∀ store, 0 < (original.localState.block store).mass →
      store = Runtime.Context.inputStore I)
    (entry : Store (Runtime.Context.pre I) × Store (Runtime.Context.pre I))
    (positive : 0 < ((original.state.mapClassical (fun store => (store, store))).block
      entry).mass) : entry.1 = Runtime.Context.inputStore I := by
  obtain ⟨store, same, present⟩ := (ExecutionState.mapClassical_block_mass_pos_iff
    original.state (fun store => (store, store)) entry).mp (by
      apply lt_of_lt_of_eq positive
      simp only [ExecutionState.mapClassical_block_mass]
      apply Finset.sum_congr rfl
      intro source _
      split_ifs <;> rfl)
  subst entry
  exact valid store ((original.localState_block_mass store).symm ▸ present)

/-- No incorrect present word has positive probability in the actual complete run. -/
theorem nativeECDLP_recoveryRun_wrong_probability_zero
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    {Reference : Register} (original : Input (Runtime.Context.pre I) Reference)
    (valid : ∀ store, 0 < (original.localState.block store).mass →
      store = Runtime.Context.inputStore I)
    (value : (CShape.unsignedWord (FiniteCyclicDLP.orderWidth (problem I))).Value)
    (different : value ≠ CShape.wordOfNat (FiniteCyclicDLP.orderWidth (problem I))
      (input I).secret.val) :
    (recoveryRun (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I) I B A
      count (Runtime.Context.baseRef I) (Runtime.Context.targetRef I)).outputDistribution
        original (.optionSome value) = 0 := by
  by_contra positive
  let run := recoveryRun (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I)
    I B A count (Runtime.Context.baseRef I) (Runtime.Context.targetRef I)
  have supported : CShape.Value.optionSome value ∈ (run.outputDistribution original).support :=
    (PMF.mem_support_iff _ _).mpr positive
  obtain ⟨record, present, output⟩ := (PMF.mem_support_map_iff run.result
    (run.executionDistribution original) (.optionSome value)).mp supported
  have mass := (ExecutionState.mem_support_toPMF_iff (run.execute Reference original.state)
    (run.execute_normalized original) record).mp present
  exact different (nativeECDLP_recoveryRun_supported_secret I B A count
    (original.state.mapClassical (fun store => (store, store))) (entered_valid I original valid)
      record mass value output)

/-- Actual final failure probability satisfies the original geometric bound for every count. -/
theorem nativeECDLP_recoveryRun_none_probability_le
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    {Reference : Register} (original : Input (Runtime.Context.pre I) Reference)
    (valid : ∀ store, 0 < (original.localState.block store).mass →
      store = Runtime.Context.inputStore I) :
    (recoveryRun (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I) I B A
      count (Runtime.Context.baseRef I) (Runtime.Context.targetRef I)).outputDistribution
        original .optionNone ≤ ENNReal.ofReal ((1 - attemptFloor (problem I)) ^ count) := by
  have contracted := nativeECDLP_recoveryRun_none_weight_le I B A count
    (original.state.mapClassical (fun store => (store, store))) (entered_valid I original valid)
  rw [ExecutionState.mapClassical_mass, original.normalized, mul_one] at contracted
  rw [AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  exact ENNReal.ofReal_le_ofReal contracted

/-- The complete actual finite run returns the original secret with its original success bound. -/
theorem nativeECDLP_recoveryRun_secret_probability_ge
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    {Reference : Register} (original : Input (Runtime.Context.pre I) Reference)
    (valid : ∀ store, 0 < (original.localState.block store).mass →
      store = Runtime.Context.inputStore I) :
    1 - ENNReal.ofReal ((1 - attemptFloor (problem I)) ^ count) ≤
      (recoveryRun (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I) I B A
        count (Runtime.Context.baseRef I) (Runtime.Context.targetRef I)).outputDistribution
          original (.optionSome (CShape.wordOfNat (FiniteCyclicDLP.orderWidth (problem I))
            (input I).secret.val)) := by
  let run := recoveryRun (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I)
    I B A count (Runtime.Context.baseRef I) (Runtime.Context.targetRef I)
  let distribution := run.outputDistribution original
  let wanted := CShape.wordOfNat (FiniteCyclicDLP.orderWidth (problem I)) (input I).secret.val
  have total : distribution .optionNone + distribution (.optionSome wanted) = 1 := by
    apply two_output_mass distribution .optionNone (.optionSome wanted) (by intro same; cases same)
    intro value absent different
    cases value with
    | optionNone => exact False.elim (absent rfl)
    | optionSome value =>
        exact nativeECDLP_recoveryRun_wrong_probability_zero I B A count original valid value
          (fun same => different (congrArg CShape.Value.optionSome same))
  have complement : 1 - distribution .optionNone ≤ distribution (.optionSome wanted) := by
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using total.symm.le
  exact (tsub_le_tsub_left
    (nativeECDLP_recoveryRun_none_probability_le I B A count original valid) 1).trans complement

/-- The original finite retry calibration reaches the original requested success threshold. -/
theorem nativeECDLP_recoveryRun_calibrated_success
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed)
    {Reference : Register} (original : Input (Runtime.Context.pre I) Reference)
    (valid : ∀ store, 0 < (original.localState.block store).mass →
      store = Runtime.Context.inputStore I) :
    Factoring.FailureBudget.successThreshold budget ≤
      (recoveryRun (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I) I B A
        (Canonical.retryCountForBudget I budget) (Runtime.Context.baseRef I)
          (Runtime.Context.targetRef I)).outputDistribution original
            (.optionSome (CShape.wordOfNat (FiniteCyclicDLP.orderWidth (problem I))
              (input I).secret.val)) := by
  have calibrated := successThreshold_le_one_sub_retryFailurePower (problem I) budget wellFormed
  have nonnegative := Factoring.FailureBudget.value_nonneg (sourceFailureBudget (problem I))
    (sourceFailureBudget_strictlyWellFormed (problem I)).toWellFormed
  rw [← ENNReal.ofReal_pow nonnegative, sourceFailureBudget_value] at calibrated
  exact calibrated.trans (nativeECDLP_recoveryRun_secret_probability_ge I B A
    (Canonical.retryCountForBudget I budget) original valid)

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
