/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Correctness
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Loop

/-!
# Actual repeated ECDLP success with the original exceptional error

The real output distribution has only two possible values: no result or the
original secret. Its actual failure bound therefore gives the original-secret
success bound on the same complete execution, with the original exceptional
error retained in every repetition coefficient.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP Canonical.Probability

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

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The original secret has the complete actual geometric success bound. -/
theorem exponentRepeatedRun_secret_probability_ge
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (count : Nat) (input : SecretInput problem) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    1 - ENNReal.ofReal ((1 - ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))) ^ count) ≤
      (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
        nontrivial count).outputDistribution
          (repeatedOracleInput E problem original)
            (.optionSome (CShape.wordOfNat (orderWidth problem) input.secret.val)) := by
  let run := exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed nontrivial count
  let supplied := repeatedOracleInput E problem original
  let distribution := run.outputDistribution supplied
  let wanted := CShape.wordOfNat (orderWidth problem) input.secret.val
  have total : distribution .optionNone + distribution (.optionSome wanted) = 1 := by
    apply two_output_mass distribution .optionNone (.optionSome wanted) (by intro same; cases same)
    intro value absent different
    cases value with
    | optionNone => exact False.elim (absent rfl)
    | optionSome value =>
        exact exponentRepeatedRun_wrong_probability_zero E fieldTail sameWidth fits odd problem
          points seed nontrivial count input original value
          (fun same => different (congrArg CShape.Value.optionSome same))
  have complement : 1 - distribution .optionNone ≤ distribution (.optionSome wanted) := by
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using total.symm.le
  exact (tsub_le_tsub_left (exponentRepeatedRun_none_probability_le E fieldTail sameWidth fits
    odd problem nontrivial points seed addends count input original) 1).trans complement

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
