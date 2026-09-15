/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Checked.Probability
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Probability
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Execution

/-!
# Original probability bounds for the actual checked secret

The original source floor and exceptional-offset error reach the optional
secret read from the complete actual quantum and checked recovery execution.
Both original public points are prescribed before the quantum program. One
fixed subgroup offset is chosen before the secret, reference and old store;
no runtime secret or additional public-value assumption is supplied.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP Canonical.Probability

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual checked-secret PMF retains the original floor and supplied-offset error. -/
theorem exponentCheckedRun_probability_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem) {Reference : Register}
    (reference : NormalizedVector Reference)
    (stored : Store (before p.size (2 * orderWidth problem))) :
    ENNReal.ofReal ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2)) ≤
      (exponentCheckedRun E fieldTail odd problem points nontrivial).outputDistribution
        (PublicInput.initialInput E (orderWidth problem) problem
          (AlgorithmRun.pureInput stored
            (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference)))
        (checkedSecretOutput problem input) +
        ENNReal.ofReal (4 * Real.sqrt (preparedExceptionalMass problem points seed)) := by
  have checked := exponentCheckedRun_selected_probability_le E fieldTail odd problem points
    nontrivial input (AlgorithmRun.pureInput stored
      (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference))
  rw [PublicInput.exponentRun_outputDistribution] at checked
  exact (selectedExponentRun_probability_bound E fieldTail sameWidth fits odd
    problem points seed addends input reference stored).trans (add_le_add checked le_rfl)

/-- One original subgroup offset works uniformly for every actual checked-secret output. -/
theorem exists_fixedOffset_exponentCheckedRun_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    ∃ seed : AffinePoint E,
      seed.toGroupPoint ∈ Subgroup.zpowers problem.generator ∧ seed.toGroupPoint ≠ 1 ∧
        ∀ (input : SecretInput problem) (Reference : Register)
          (reference : NormalizedVector Reference)
          (stored : Store (before p.size (2 * orderWidth problem))),
          ENNReal.ofReal ((problem.order : ℝ) * Nat.totient problem.order /
            (4 * (fourierModulus problem : ℝ) ^ 2)) ≤
            (exponentCheckedRun E fieldTail odd problem points nontrivial).outputDistribution
              (PublicInput.initialInput E (orderWidth problem) problem
                (AlgorithmRun.pureInput stored
                  (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference)))
              (checkedSecretOutput problem input) +
              ENNReal.ofReal (4 * Real.sqrt
                ((2 * (2 * orderWidth problem) : Nat) / ((problem.order - 1 : Nat) : ℝ))) := by
  obtain ⟨seed, member, nonidentity, bound⟩ :=
    exists_fixedOffset_selectedExponentRun_bound E fieldTail sameWidth fits odd
      problem nontrivial points addends
  refine ⟨seed, member, nonidentity, ?_⟩
  intro input Reference reference stored
  have checked := exponentCheckedRun_selected_probability_le E fieldTail odd problem points
    nontrivial input (AlgorithmRun.pureInput stored
      (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference))
  rw [PublicInput.exponentRun_outputDistribution] at checked
  exact (bound input Reference reference stored).trans (add_le_add checked le_rfl)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
