/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
public import QuantumAlg.Util.Real.Geometric
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Probability
import all QuantumAlg.Algorithms.Factoring.Common

/-!
# Real failure targets for the declared Shor machine

The signed logarithm quotient chooses the actual natural number of attempts.
A target of one selects zero attempts. The rational source floor is unchanged.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine.RealTarget

noncomputable section

/-- The direct real-target retry count, including the zero-attempt boundary. -/
public def repetitionCount (N : Nat) (η : Real) : Nat :=
  ⌈Real.log η / Real.log (1 - 1 / (48 * (modulusBits N : Real)))⌉₊

/-- The direct real logarithmic count meets the unchanged certified source failure floor. -/
lemma repetition_failure_le {N : Nat} (input : Input N) (η : Real) (positive : 0 < η) :
    (ENNReal.ofReal (sourceFailureBudget N).value) ^ repetitionCount N η ≤
      ENNReal.ofReal η := by
  have valid := sourceFailureBudget_strictlyWellFormed input
  have valuePositive := FailureBudget.value_pos (sourceFailureBudget N) valid.toWellFormed
  have valueBelow : (sourceFailureBudget N).value < 1 := by
    unfold FailureBudget.value
    apply (div_lt_one (by exact_mod_cast valid.denominator_pos)).mpr
    exact_mod_cast valid.numerator_lt_denominator
  rw [← ENNReal.ofReal_pow valuePositive.le]
  apply ENNReal.ofReal_le_ofReal
  have count : repetitionCount N η =
      ⌈Real.log η / Real.log (sourceFailureBudget N).value⌉₊ := by
    rw [Probability.sourceFailureBudget_value input]
    simp only [repetitionCount, sourceSuccessDenominator, Nat.cast_mul, Nat.cast_ofNat]
  rw [count]
  exact RealLog.pow_natCeil_logRatio_le valuePositive valueBelow positive

/-- The unit target uses the genuine zero-round machine. -/
public lemma shorRealTarget_repetitionCount_one (N : Nat) : repetitionCount N 1 = 0 := by
  simp [repetitionCount]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine.RealTarget
