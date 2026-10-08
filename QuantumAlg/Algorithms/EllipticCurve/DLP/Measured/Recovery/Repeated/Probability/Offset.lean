/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Offset
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Success

/-!
# One original fixed offset for actual repeated success

Finite averaging selects the same nonidentity subgroup seed before any
iteration count, secret witness, reference or original input is chosen.
The actual repeated success bound retains the original two-exceptions-per-step
constant and complete four-square-root error. No positive-floor or additional
retry-calibration domain is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP Canonical.Probability

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] exponentRepeatedRun repeatedOracleInput
  AlgorithmRun.outputDistribution

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

private theorem exceptional_complement_le {floor exceptional upper : ℝ}
    (nonnegative : 0 ≤ 1 - (floor - 4 * Real.sqrt exceptional))
    (bounded : exceptional ≤ upper) (count : Nat) :
    1 - ENNReal.ofReal ((1 - (floor - 4 * Real.sqrt upper)) ^ count) ≤
      1 - ENNReal.ofReal ((1 - (floor - 4 * Real.sqrt exceptional)) ^ count) := by
  have errorBound : 4 * Real.sqrt exceptional ≤ 4 * Real.sqrt upper :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt bounded) (by norm_num)
  have ratioBound : 1 - (floor - 4 * Real.sqrt exceptional) ≤
      1 - (floor - 4 * Real.sqrt upper) :=
    sub_le_sub_left (sub_le_sub_left errorBound _) _
  exact tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ nonnegative ratioBound count)) 1

private theorem fixedOffset_probability_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (massBound : preparedExceptionalMass problem points seed ≤
      (2 * (2 * orderWidth problem) : Nat) / ((problem.order - 1 : Nat) : ℝ))
    (count : Nat) (input : SecretInput problem) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    1 - ENNReal.ofReal ((1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt ((2 * (2 * orderWidth problem) : Nat) /
          ((problem.order - 1 : Nat) : ℝ)))) ^ count) ≤
      (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
        nontrivial count).outputDistribution
          (repeatedOracleInput E problem original)
            (.optionSome (CShape.wordOfNat (orderWidth problem) input.secret.val)) := by
  have originalBound := exponentRepeatedRun_secret_probability_ge E fieldTail sameWidth fits
    odd problem nontrivial points seed addends count input original
  exact (exceptional_complement_le
    (samplingFailureRatio_nonneg problem points seed) massBound count).trans originalBound


/-- One original fixed seed gives the same complete success bound for every actual finite run. -/
theorem exists_fixedOffset_repeated_secret_probability_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    ∃ seed : AffinePoint E,
      seed.toGroupPoint ∈ Subgroup.zpowers problem.generator ∧ seed.toGroupPoint ≠ 1 ∧
        ∀ (count : Nat) (input : SecretInput problem) (Reference : Register)
          (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference),
          1 - ENNReal.ofReal ((1 - ((problem.order : ℝ) * Nat.totient problem.order /
            (4 * (fourierModulus problem : ℝ) ^ 2) -
              4 * Real.sqrt ((2 * (2 * orderWidth problem) : Nat) /
                ((problem.order - 1 : Nat) : ℝ)))) ^ count) ≤
            (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
              nontrivial count).outputDistribution
                (repeatedOracleInput E problem original)
                  (.optionSome (CShape.wordOfNat (orderWidth problem) input.secret.val)) := by
  obtain ⟨seed, member, nonidentity, massBound⟩ :=
    exists_fixedOffset_exceptionalMass_bound problem nontrivial points
  refine ⟨seed, member, nonidentity, ?_⟩
  intro count input Reference original
  exact fixedOffset_probability_bound E fieldTail sameWidth fits odd problem nontrivial
    points seed addends massBound count input original

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
