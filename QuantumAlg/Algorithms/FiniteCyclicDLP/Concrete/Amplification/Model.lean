/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.Factoring.Common
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Selected
import all QuantumAlg.Algorithms.FiniteCyclicDLP.PrimeOrderTailBound

/-!
# Exact selected-family retry calibration

The original rational floor and its failure complement determine the
finite retry count. These numerical lemmas require no execution wrapper
or independent-sampler assumption.
-/

namespace QuantumAlg

open Factoring

noncomputable section

namespace FiniteCyclicDLP.Concrete.Amplification

universe u

variable {G : Type u} [Group G]

/-- Natural denominator of the concrete selected-family one-attempt floor. -/
def successDenominator (P : KnownOrderProblem G) : Nat :=
  4 * fourierModulus P ^ 2

/-- Number of selected `(tail, unit)` pairs in the one-attempt floor. -/
def successNumerator (P : KnownOrderProblem G) : Nat :=
  P.order * Nat.totient P.order

/-- Real form of the concrete selected-family one-attempt floor. -/
def attemptFloor (P : KnownOrderProblem G) : Real :=
  (successNumerator P : Real) / successDenominator P

/-- Exact rational complement of the concrete selected-family floor. -/
def sourceFailureBudget (P : KnownOrderProblem G) : FailureBudget where
  failureNumerator := successDenominator P - successNumerator P
  failureDenominator := successDenominator P

theorem successNumerator_lt_successDenominator (P : KnownOrderProblem G) :
    successNumerator P < successDenominator P := by
  have htotient : Nat.totient P.order ≤ P.order := Nat.totient_le P.order
  have horder : P.order ≤ fourierModulus P := order_le_fourierModulus P
  have hmodulus : 0 < fourierModulus P := by
    unfold fourierModulus
    positivity
  unfold successNumerator successDenominator
  nlinarith

/-- For prime order `r`, the general selected-tail floor is exactly
`r(r-1)/(4q²)`. -/
theorem attemptFloor_eq_primeOrder (P : KnownOrderProblem G)
    (hprime : P.order.Prime) :
    attemptFloor P =
      ((P.order * (P.order - 1) : Nat) : Real) / successDenominator P := by
  rw [attemptFloor, successNumerator, Nat.totient_prime hprime]

/-- At prime order, the concrete selected-family failure complement is the
shared parameterized `r,q` budget. -/
theorem sourceFailureBudget_eq_primeOrder (P : KnownOrderProblem G)
    (hprime : P.order.Prime) :
    sourceFailureBudget P =
      PrimeOrderTailBound.sourceFailureBudget
        P.order (fourierModulus P) := by
  simp [sourceFailureBudget, successDenominator, successNumerator,
    PrimeOrderTailBound.sourceFailureBudget,
    PrimeOrderTailBound.successDenominator,
    PrimeOrderTailBound.successNumerator, Nat.totient_prime hprime]

/-- The concrete selected-family floor is exactly the advertised positive
rational. -/
theorem selectedOutcomeFamilyLowerBound_eq_ofReal_attemptFloor
    (P : KnownOrderProblem G) :
    FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound P =
      ENNReal.ofReal (attemptFloor P) := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  unfold FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound
    Canonical.Probability.selectedRawOutcomeFamilyLowerBound
    Canonical.Probability.selectedRawOutcomePointwiseLowerBound
    Canonical.Probability.selectedTailPointwiseLowerBound attemptFloor
  rw [ZMod.card_units_eq_totient, ← ENNReal.ofReal_nsmul,
    ← ENNReal.ofReal_nsmul]
  congr 1
  simp only [nsmul_eq_mul]
  unfold successNumerator successDenominator
  norm_num
  ring

theorem sourceFailureBudget_strictlyWellFormed
    (P : KnownOrderProblem G) :
    (sourceFailureBudget P).StrictlyWellFormed := by
  have hden : 0 < successDenominator P := by
    unfold successDenominator fourierModulus
    positivity
  have htotient : 0 < Nat.totient P.order :=
    Nat.totient_pos.mpr P.order_pos
  have hsuccess : 0 < successNumerator P := by
    unfold successNumerator
    exact Nat.mul_pos P.order_pos htotient
  have hlt := successNumerator_lt_successDenominator P
  refine
    { toWellFormed :=
        { numerator_pos := ?_
          denominator_pos := ?_
          numerator_le_denominator := ?_ }
      numerator_lt_denominator := ?_ }
  · simp only [sourceFailureBudget]
    omega
  · simpa only [sourceFailureBudget] using hden
  · simp only [sourceFailureBudget]
    omega
  · simp only [sourceFailureBudget]
    omega

theorem sourceFailureBudget_value (P : KnownOrderProblem G) :
    (sourceFailureBudget P).value = 1 - attemptFloor P := by
  have hle : successNumerator P ≤ successDenominator P :=
    (successNumerator_lt_successDenominator P).le
  have hden : (successDenominator P : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (sourceFailureBudget_strictlyWellFormed P).denominator_pos)
  unfold sourceFailureBudget FailureBudget.value attemptFloor
  rw [Nat.cast_sub hle]
  field_simp

/-- The actual concrete floor has exactly the failure complement used for
retry calibration. -/
theorem one_sub_selectedOutcomeFamilyLowerBound_eq_sourceFailure
    (P : KnownOrderProblem G) :
    1 - FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound P =
      ENNReal.ofReal (sourceFailureBudget P).value := by
  rw [selectedOutcomeFamilyLowerBound_eq_ofReal_attemptFloor,
    sourceFailureBudget_value]
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by
      unfold attemptFloor
      positivity : 0 ≤ attemptFloor P)]

/-- Exact internal repeat count for any well-formed public failure budget. -/
def retryCountForBudget (P : KnownOrderProblem G)
    (budget : FailureBudget) : Nat :=
  FailureBudget.retryCountFor (sourceFailureBudget P) budget

/-- Prime-order concrete endpoints consume the shared `r,q,eta` retry count
without an endpoint-specific calibration. -/
theorem retryCountForBudget_eq_primeOrder (P : KnownOrderProblem G)
    (budget : FailureBudget) (hprime : P.order.Prime) :
    retryCountForBudget P budget =
      PrimeOrderTailBound.retryCount
        P.order (fourierModulus P) budget := by
  unfold retryCountForBudget PrimeOrderTailBound.retryCount
  rw [sourceFailureBudget_eq_primeOrder P hprime]

theorem retryFailurePower_le_budget (P : KnownOrderProblem G)
    (budget : FailureBudget) (hbudget : budget.WellFormed) :
    (ENNReal.ofReal (sourceFailureBudget P).value) ^
        retryCountForBudget P budget ≤
      ENNReal.ofReal budget.value := by
  simpa [retryCountForBudget] using
    FailureBudget.retryFailurePowerFor_le
      (sourceFailureBudget P) budget
      (sourceFailureBudget_strictlyWellFormed P) hbudget

theorem successThreshold_le_one_sub_retryFailurePower
    (P : KnownOrderProblem G) (budget : FailureBudget)
    (hbudget : budget.WellFormed) :
    FailureBudget.successThreshold budget ≤
      1 - (ENNReal.ofReal (sourceFailureBudget P).value) ^
        retryCountForBudget P budget := by
  rw [FailureBudget.successThreshold,
    ENNReal.ofReal_sub _ (FailureBudget.value_nonneg budget hbudget),
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left (retryFailurePower_le_budget P budget hbudget) 1

end FiniteCyclicDLP.Concrete.Amplification

end

end QuantumAlg
