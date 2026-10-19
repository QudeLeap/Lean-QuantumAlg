/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Distribution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Calibration
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Recovery
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Probability

/-!
# Actual factoring success for every natural number of attempts

The original machine law and original source recovery proof apply to any
positive count. At zero the asserted success floor is zero; initialization
and output packing still belong to the genuine machine execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine.RealTarget

open Execution
noncomputable section

/-- Every actual count attains the geometric lower bound of the existing source floor. -/
lemma output_success_ge_power (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (count : Nat)
    {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles base Reference) :
    1 - (ENNReal.ofReal (sourceFailureBudget N).value) ^ count ≤
      ((run base noQuantum N (Probability.Input.ofSemiprimeModel model) count).outputDistribution
        (environment (Probability.Input.ofSemiprimeModel model)) original).toOuterMeasure
          {value | Probability.ReturnedDeclaredFactor model value} := by
  cases count with
  | zero => simp
  | succ further =>
      let source := Probability.Input.ofSemiprimeModel model
      let count := further + 1
      let sampling := PMF.independentReplicateVector (sourceOutcomePMF source) count
      let result := fun samples : List.Vector (SourceOutcome N) count =>
        NativeFactorScan.sourceResults source samples.toList
      let accepted : Set (CShape.Value (.option (.unsignedWord (modulusBits N)))) :=
        {value | Probability.ReturnedDeclaredFactor model value}
      have actual : ((run base noQuantum N source count).outputDistribution
          (environment source) original).toOuterMeasure accepted = sampling.toOuterMeasure
            (result ⁻¹' accepted) :=
        (congrArg (fun distribution :
          PMF (CShape.Value (.option (.unsignedWord (modulusBits N)))) =>
          distribution.toOuterMeasure accepted)
          (outputDistribution_eq base noQuantum N source count original)).trans
            (PMF.toOuterMeasure_map_apply result sampling accepted)
      change 1 - (ENNReal.ofReal (sourceFailureBudget N).value) ^ count ≤
        ((run base noQuantum N source count).outputDistribution
          (environment (Probability.Input.ofSemiprimeModel model)) original).toOuterMeasure accepted
      rw [actual]
      by_cases even : Even N
      · have allAccepted : result ⁻¹' accepted = Set.univ := by
          apply Set.eq_univ_of_forall
          intro samples
          have nonempty : samples.toList ≠ [] := by
            intro empty
            have length := samples.2
            change samples.toList.length = further + 1 at length
            rw [empty] at length
            simp at length
          cases listed : samples.toList with
          | nil => exact False.elim (nonempty listed)
          | cons head rest =>
              change Probability.ReturnedDeclaredFactor model
                (NativeFactorScan.sourceResults source samples.toList)
              rw [listed]
              exact NativeFactorScan.sourceResults_of_even model even head rest
        rw [allAccepted, PMF.toOuterMeasure_apply]
        simp
      · have bounded := Probability.sourceRepeat_containsEvent_probability_ge source
          (Probability.GoodAttemptOutcome model) count (Probability.honestAttemptSuccessFloor N)
          (1 - (ENNReal.ofReal (sourceFailureBudget N).value) ^ count)
          (Probability.honestAttemptSuccessFloor_le_goodOutcomeProbability model even)
          (by rw [Probability.one_sub_attemptFloor_eq_sourceFailure source])
        refine bounded.trans (MeasureTheory.measure_mono ?_)
        intro samples good
        exact NativeFactorScan.sourceResults_of_contains_good model samples.toList good

/-- Arbitrary positive real targets select the same genuine initialized complete execution. -/
lemma output_success_ge_real (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (η : Real) (positive : 0 < η) {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles base Reference) :
    ENNReal.ofReal (1 - η) ≤
      ((run base noQuantum N (Probability.Input.ofSemiprimeModel model)
        (repetitionCount N η)).outputDistribution
          (environment (Probability.Input.ofSemiprimeModel model)) original).toOuterMeasure
          {value | Probability.ReturnedDeclaredFactor model value} := by
  rw [ENNReal.ofReal_sub _ positive.le, ENNReal.ofReal_one]
  exact (tsub_le_tsub_left
    (repetition_failure_le (Probability.Input.ofSemiprimeModel model) η positive) 1).trans
      (output_success_ge_power base noQuantum model (repetitionCount N η) original)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine.RealTarget
