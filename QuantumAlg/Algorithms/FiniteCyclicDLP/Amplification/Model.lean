/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.Common
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Selected
import all QuantumAlg.Algorithms.FiniteCyclicDLP.PrimeOrderTailBound

/-!
# Original finite-cyclic retry calibration and two-thirds threshold

The original selected-family floor, its conservative public totient floor
and their exact rational complements retain the original fixed retry count.
These pure identities do not import a prepared execution or assert that
runtime samples are independent. The original terminal Born bound is separate.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical

open Factoring

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Natural denominator of the canonical selected-family one-attempt floor. -/
def successDenominator (P : KnownOrderProblem G) : Nat :=
  4 * fourierModulus P ^ 2

/-- Number of selected `(tail, unit)` pairs in the one-attempt floor. -/
def successNumerator (P : KnownOrderProblem G) : Nat :=
  P.order * Nat.totient P.order

/-- Real form of the summed selected-family one-attempt floor. -/
def attemptFloor (P : KnownOrderProblem G) : Real :=
  (successNumerator P : Real) / successDenominator P

/-- Exact rational complement of the canonical selected-family floor. -/
def sourceFailureBudget (P : KnownOrderProblem G) : FailureBudget where
  failureNumerator := successDenominator P - successNumerator P
  failureDenominator := successDenominator P

/-- Conservative numerator used by the public fixed-two-thirds retry formula.
It retains one certified selected outcome for each invertible residue. -/
def publicSuccessNumerator (P : KnownOrderProblem G) : Nat :=
  Nat.totient P.order

/-- Conservative one-attempt failure budget displayed by the public endpoint.
The actual selected-family floor is stronger by the factor `P.order`. -/
def publicFailureBudget (P : KnownOrderProblem G) : FailureBudget where
  failureNumerator := successDenominator P - publicSuccessNumerator P
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

theorem publicSuccessNumerator_le_successNumerator
    (P : KnownOrderProblem G) :
    publicSuccessNumerator P ≤ successNumerator P := by
  have horder : 1 ≤ P.order := P.order_pos
  unfold publicSuccessNumerator successNumerator
  nlinarith [Nat.zero_le (Nat.totient P.order)]

theorem publicSuccessNumerator_lt_successDenominator
    (P : KnownOrderProblem G) :
    publicSuccessNumerator P < successDenominator P :=
  (publicSuccessNumerator_le_successNumerator P).trans_lt
    (successNumerator_lt_successDenominator P)

/-- For prime order `r`, the general selected-tail floor is exactly
`r(r-1)/(4q²)`. -/
theorem attemptFloor_eq_primeOrder (P : KnownOrderProblem G)
    (hprime : P.order.Prime) :
    attemptFloor P =
      ((P.order * (P.order - 1) : Nat) : Real) / successDenominator P := by
  rw [attemptFloor, successNumerator, Nat.totient_prime hprime]

/-- At prime order, the canonical selected-family failure complement is the
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

/-- The selected-family floor is exactly the advertised positive rational. -/
theorem selectedRawOutcomeFamilyLowerBound_eq_ofReal_attemptFloor
    (P : KnownOrderProblem G) :
    Probability.selectedRawOutcomeFamilyLowerBound P =
      ENNReal.ofReal (attemptFloor P) := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  unfold Probability.selectedRawOutcomeFamilyLowerBound
    Probability.selectedRawOutcomePointwiseLowerBound
    Probability.selectedTailPointwiseLowerBound attemptFloor
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

theorem publicFailureBudget_strictlyWellFormed
    (P : KnownOrderProblem G) :
    (publicFailureBudget P).StrictlyWellFormed := by
  have hden : 0 < successDenominator P := by
    unfold successDenominator fourierModulus
    positivity
  have hsuccess : 0 < publicSuccessNumerator P := by
    unfold publicSuccessNumerator
    exact Nat.totient_pos.mpr P.order_pos
  have hlt := publicSuccessNumerator_lt_successDenominator P
  refine
    { toWellFormed :=
        { numerator_pos := ?_
          denominator_pos := ?_
          numerator_le_denominator := ?_ }
      numerator_lt_denominator := ?_ }
  · simp only [publicFailureBudget]
    omega
  · simpa only [publicFailureBudget] using hden
  · simp only [publicFailureBudget]
    omega
  · simp only [publicFailureBudget]
    omega

theorem sourceFailureBudget_value_le_publicFailureBudget_value
    (P : KnownOrderProblem G) :
    (sourceFailureBudget P).value ≤ (publicFailureBudget P).value := by
  have hnumerator :
      successDenominator P - successNumerator P ≤
        successDenominator P - publicSuccessNumerator P :=
    Nat.sub_le_sub_left (publicSuccessNumerator_le_successNumerator P) _
  have hcast :
      ((successDenominator P - successNumerator P : Nat) : Real) ≤
        ((successDenominator P - publicSuccessNumerator P : Nat) : Real) := by
    exact_mod_cast hnumerator
  have hden : (0 : Real) < successDenominator P := by
    exact_mod_cast (publicFailureBudget_strictlyWellFormed P).denominator_pos
  unfold sourceFailureBudget publicFailureBudget FailureBudget.value
  exact (div_le_div_iff_of_pos_right hden).2 hcast

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

/-- The actual canonical raw floor has exactly the failure complement used
for retry calibration. -/
theorem one_sub_selectedRawOutcomeFamilyLowerBound_eq_sourceFailure
    (P : KnownOrderProblem G) :
    1 - Probability.selectedRawOutcomeFamilyLowerBound P =
      ENNReal.ofReal (sourceFailureBudget P).value := by
  rw [selectedRawOutcomeFamilyLowerBound_eq_ofReal_attemptFloor,
    sourceFailureBudget_value]
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by
      unfold attemptFloor
      positivity : 0 ≤ attemptFloor P)]

/-- Exact internal repeat count from the conservative public floor and the
fixed one-third failure target. -/
def retryCount (P : KnownOrderProblem G) : Nat :=
  FailureBudget.retryCountFor (publicFailureBudget P) FailureBudget.oneThird

/-- Closed form displayed by the public finite-cyclic endpoint. -/
theorem retryCount_eq_closedForm (P : KnownOrderProblem G) :
    retryCount P =
      max 1 (Nat.ceil
        (Real.log 3 /
          Real.log
            ((successDenominator P : Real) /
              ((successDenominator P - Nat.totient P.order : Nat) : Real)))) := by
  simp [retryCount, FailureBudget.retryCountFor,
    FailureBudget.retryExponentFor, FailureBudget.oneThird,
    publicFailureBudget, publicSuccessNumerator]

/-- Exact internal repeat count for any well-formed public failure budget. -/
def retryCountForBudget (P : KnownOrderProblem G)
    (budget : FailureBudget) : Nat :=
  FailureBudget.retryCountFor (sourceFailureBudget P) budget

/-- Prime-order canonical endpoints consume the shared `r,q,eta` retry count
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

theorem retryCount_pos (P : KnownOrderProblem G) : 0 < retryCount P :=
  FailureBudget.retryCountFor_pos _ _

@[simp] theorem retryCount_ne_zero (P : KnownOrderProblem G) :
    retryCount P ≠ 0 :=
  Nat.ne_of_gt (retryCount_pos P)

theorem retryFailurePower_le_oneThird (P : KnownOrderProblem G) :
    (ENNReal.ofReal (sourceFailureBudget P).value) ^ retryCount P ≤
      ENNReal.ofReal ((1 : Real) / 3) := by
  calc
    (ENNReal.ofReal (sourceFailureBudget P).value) ^ retryCount P ≤
        (ENNReal.ofReal (publicFailureBudget P).value) ^ retryCount P :=
      pow_le_pow_left'
        (ENNReal.ofReal_le_ofReal
          (sourceFailureBudget_value_le_publicFailureBudget_value P)) _
    _ ≤ ENNReal.ofReal ((1 : Real) / 3) := by
      simpa [retryCount] using
        FailureBudget.retryFailurePowerFor_le
          (publicFailureBudget P) FailureBudget.oneThird
          (publicFailureBudget_strictlyWellFormed P)
          FailureBudget.oneThird_wellFormed

theorem twoThirds_le_one_sub_retryFailurePower
    (P : KnownOrderProblem G) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      1 - (ENNReal.ofReal (sourceFailureBudget P).value) ^ retryCount P := by
  rw [FailureBudget.twoThirds_eq_one_sub_oneThird]
  exact tsub_le_tsub_left (retryFailurePower_le_oneThird P) 1

end

end QuantumAlg.FiniteCyclicDLP.Canonical
