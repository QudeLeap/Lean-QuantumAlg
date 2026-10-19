/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Success
public import QuantumAlg.Util.Real.Geometric
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Success
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.SuccessFloor
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Amplification.Model
import all QuantumAlg.Algorithms.Factoring.Common

/-!
# Direct real failure calibration for the declared ECDLP execution

Only this local endpoint chooses the direct logarithmic ceiling, including
zero at a unit failure target. The shared rational retry definitions and every
native curve or fixed-instance execution remain unchanged.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section
open Execution
variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The local real target chooses the actual number of complete original rounds. -/
public def realRepetitionCount (I : ECDLPInstance E) (η : Real) : Nat :=
  ⌈Real.log η / Real.log (1 - Sampling.Reuse.successFloor I)⌉₊

/-- The known selected-family failure complement lies strictly between zero and one. -/
lemma realFailure_in_unitInterval (I : ECDLPInstance E) :
    0 < 1 - Sampling.Reuse.successFloor I ∧ 1 - Sampling.Reuse.successFloor I < 1 := by
  let source := FiniteCyclicDLP.Concrete.Amplification.sourceFailureBudget (problem I)
  have valid := FiniteCyclicDLP.Concrete.Amplification.sourceFailureBudget_strictlyWellFormed
    (problem I)
  have same : source.value = 1 - Sampling.Reuse.successFloor I :=
    FiniteCyclicDLP.Concrete.Amplification.sourceFailureBudget_value (problem I)
  rw [← same]
  constructor
  · exact Factoring.FailureBudget.value_pos source valid.toWellFormed
  · unfold Factoring.FailureBudget.value
    apply (div_lt_one (by exact_mod_cast valid.denominator_pos)).mpr
    exact_mod_cast valid.numerator_lt_denominator

/-- The selected count attains the requested real failure tolerance. -/
lemma realRepetition_failure_le (I : ECDLPInstance E) (η : Real) (positive : 0 < η) :
    (1 - Sampling.Reuse.successFloor I) ^ realRepetitionCount I η ≤ η :=
  RealLog.pow_natCeil_logRatio_le (realFailure_in_unitInterval I).1
    (realFailure_in_unitInterval I).2 positive

/-- The complete initialized zero-round execution is selected at the unit target. -/
public lemma ecdlpReal_repetitionCount_one (I : ECDLPInstance E) :
    realRepetitionCount I 1 = 0 := by
  simp [realRepetitionCount]

/-- Real-target calibration applies directly to the original full input/output distribution. -/
lemma ecdlpRecovery_run_real_success (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (η : Real) (positive : 0 < η)
    {Reference : Register}
    (original : OracleInput (Sampling.executionModel I).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState) :
    ENNReal.ofReal (1 - η) ≤
      ((run I expansion nontrivial (realRepetitionCount I η)).relationalDistribution
        (Sampling.sourceEnvironment I A) original).toOuterMeasure {pair | wholeAccepts I pair.2}
        := by
  rw [ENNReal.ofReal_sub _ positive.le, ENNReal.ofReal_one]
  exact (tsub_le_tsub_left (ENNReal.ofReal_le_ofReal
    (realRepetition_failure_le I η positive)) 1).trans
      (ecdlpRecovery_run_success I A expansion nontrivial (realRepetitionCount I η) original valid)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
