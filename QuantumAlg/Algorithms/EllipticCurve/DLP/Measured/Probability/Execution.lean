/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Bound
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Comparison.Agreement
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Comparison.Prepared

/-!
# Original selected-frequency bounds for actual measured exponent outputs

The actual run prepares the original exponent state, executes the measured
Montgomery scalar circuit, applies the original inverse Fourier transforms,
and returns its own retained measurement cells. Its true output PMF inherits
the original selected-frequency lower bound and the original exceptional
offset error, by complete coherent agreement with the original group target.

The secret witness identifies a mathematical event in these outputs; it is
absent from the executable run. The conclusions here concern measured
exponent frequencies, before subsequent classical discrete-log recovery.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP Canonical.Probability

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Each supplied original offset retains the original source floor and its exact omitted error. -/
theorem selectedExponentRun_probability_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem) {Reference : Register}
    (reference : NormalizedVector Reference)
    (stored : Store (before p.size (2 * orderWidth problem))) :
    ENNReal.ofReal ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2)) ≤
      ((exponentRun E fieldTail odd problem points).outputDistribution
        (AlgorithmRun.pureInput stored
          (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference))).map
            (fun value => selectedExponentEvent problem input (QubitReadouts.mask value)) true +
        ENNReal.ofReal (4 * Real.sqrt (preparedExceptionalMass problem points seed)) := by
  have comparison := idealEventWeight_le_originalRunProbability_add E fieldTail sameWidth fits
    odd problem points seed reference stored
    (idealInputEffect problem fieldTail sameWidth fits seed
      (selectedExponentEvent problem input) Reference)
    (selectedExponentEvent problem input)
    (idealInputEffect_goodAgreement problem fieldTail sameWidth fits odd points seed addends
      (selectedExponentEvent problem input) reference)
  exact (ENNReal.ofReal_le_ofReal
    (idealInputEffect_selected_lower problem fieldTail sameWidth fits seed input reference)).trans
      comparison

/-- One original subgroup offset works uniformly for every witness, reference, and old store. -/
theorem exists_fixedOffset_selectedExponentRun_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (orderAtLeastTwo : 2 ≤ problem.order)
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
          ((exponentRun E fieldTail odd problem points).outputDistribution
            (AlgorithmRun.pureInput stored
              (originalMontgomeryInputVector problem fieldTail sameWidth fits
                seed reference))).map
                  (fun value => selectedExponentEvent problem input
                    (QubitReadouts.mask value)) true +
            ENNReal.ofReal (4 * Real.sqrt
              ((2 * (2 * orderWidth problem) : Nat) / ((problem.order - 1 : Nat) : ℝ))) := by
  obtain ⟨seed, member, nonidentity, massBound⟩ :=
    exists_fixedOffset_exceptionalMass_bound problem orderAtLeastTwo points
  refine ⟨seed, member, nonidentity, ?_⟩
  intro input Reference reference stored
  have comparison := selectedExponentRun_probability_bound E fieldTail sameWidth fits odd
    problem points seed addends input reference stored
  have omittedBound : 4 * Real.sqrt (preparedExceptionalMass problem points seed) ≤
      4 * Real.sqrt
        ((2 * (2 * orderWidth problem) : Nat) / ((problem.order - 1 : Nat) : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt massBound) (by norm_num)
  exact comparison.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal omittedBound))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
