/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.Factoring.ShorStyle
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Probability

/-!
# Canonical factor-15 example

This example specializes the closed Shor factoring endpoint to the public
modulus `15 = 3 * 5`. The two factors occur only in the proof-side semiprime
model; the endpoint samples its own runtime parameter and has no caller-supplied
base, order, circuit access witness, or measurement distribution.
-/

section

namespace QuantumAlg
namespace Factoring
namespace Example

noncomputable section

/-- Public modulus of the fixed factoring example. -/
def modulus : Nat := 15

/-- The public semiprime model `15 = 3 * 5`. -/
def semiprimeModel : NumberTheory.Factoring.SemiprimeFactorModel modulus := by
  exact ShorStyle.semiprimeModelOfDistinctPrimes
    (by norm_num : Nat.Prime 3)
    (by norm_num : Nat.Prime 5)
    (by norm_num : (3 : Nat) ≠ 5)
    (by norm_num [modulus] : modulus = 3 * 5)

/-- The proof-only nontrivial-modulus input assembled from the semiprime model.
It is not a caller-supplied algorithm input. -/
theorem canonicalInput : ShorStyle.Canonical.Input modulus :=
  ShorStyle.Canonical.Probability.Input.ofSemiprimeModel semiprimeModel

/-- The canonical modulus register has four bits at `N = 15`. -/
@[simp] theorem modulusBits_eq_four :
    ShorStyle.Canonical.modulusBits modulus = 4 := by
  norm_num [ShorStyle.Canonical.modulusBits, modulus]

/-- The canonical phase register has eight bits at `N = 15`. -/
@[simp] theorem phaseBits_eq_eight :
    ShorStyle.Canonical.phaseBits modulus = 8 := by
  norm_num [ShorStyle.Canonical.phaseBits,
    ShorStyle.Canonical.modulusBits, modulus]

/-- Fixed one-percent failure budget for the concrete endpoint. -/
def publishedFailureBudget : FailureBudget where
  failureNumerator := 1
  failureDenominator := 100

theorem publishedFailureBudget_wellFormed :
    publishedFailureBudget.WellFormed := by
  constructor <;> norm_num [publishedFailureBudget]

/-- Exact rational form of the fixed public success threshold. -/
theorem publishedThreshold_eq_ninetyNineHundredths :
    FailureBudget.successThreshold publishedFailureBudget =
      ENNReal.ofReal ((99 : Real) / 100) := by
  unfold FailureBudget.successThreshold FailureBudget.value
    publishedFailureBudget
  congr 1
  norm_num

/-- The typed closed Shor endpoint solves the semiprime factoring problem for
any well-formed public failure budget. -/
theorem mainForBudget (budget : FailureBudget)
    (hbudget : FailureBudget.WellFormed budget) :
    ∃ candidate : Algorithm (ShorStyle.executionModel semiprimeModel) ShorStyle.pre
        (ShorStyle.post semiprimeModel budget) (ShorStyle.OutputShape modulus),
      Algorithm.Solves candidate (ShorStyle.problem semiprimeModel budget hbudget) :=
  ⟨ShorStyle.algorithm semiprimeModel budget,
    ShorStyle.algorithm_solves semiprimeModel budget hbudget⟩

/-- The complete factor-15 specialization at the fixed one-percent failure budget. -/
theorem main :
    ∃ candidate : Algorithm (ShorStyle.executionModel semiprimeModel) ShorStyle.pre
        (ShorStyle.post semiprimeModel publishedFailureBudget) (ShorStyle.OutputShape modulus),
      Algorithm.Solves candidate
        (ShorStyle.problem semiprimeModel publishedFailureBudget
          publishedFailureBudget_wellFormed) :=
  mainForBudget publishedFailureBudget publishedFailureBudget_wellFormed

end

end Example
end Factoring
end QuantumAlg

end
