/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Probability

/-!
# Original probability lower bounds for actual measured raw recovery

The original source floor and exceptional-offset error hold for the optional
secret and true reconstruction flag read from the actual retained recovery
result. The original fixed offset is chosen before the secret witness,
external reference and old classical store. This endpoint remains before
the subsequent elliptic-curve candidate check and first-success retry.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP Canonical.Probability

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

private abbrev RecoveryModel : ExecutionModel :=
  .quantum AlgorithmGate.model .empty BitWord.model

/-- The actual recovered-secret PMF retains the original floor and supplied-offset error. -/
theorem exponentRecoveryRun_probability_bound
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
      (exponentRecoveryRun E fieldTail odd problem points nontrivial).outputDistribution
        (AlgorithmRun.pureInput (model := RecoveryModel) (stored, ())
          (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference))
        (recoveredSecretOutput problem input) +
        ENNReal.ofReal (4 * Real.sqrt (preparedExceptionalMass problem points seed)) := by
  exact (selectedExponentRun_probability_bound E fieldTail sameWidth fits odd
    problem points seed addends input reference stored).trans
      (add_le_add
        (exponentRecoveryRun_selected_probability_le (p := p) (E := E)
          (Reference := Reference) fieldTail odd problem points nontrivial
          input (AlgorithmRun.pureInput (model := RecoveryModel) (stored, ())
            (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference)))
        le_rfl)

/-- One original subgroup offset works uniformly for every actual recovered-secret output. -/
theorem exists_fixedOffset_exponentRecoveryRun_bound
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
            (exponentRecoveryRun E fieldTail odd problem points nontrivial).outputDistribution
              (AlgorithmRun.pureInput (model := RecoveryModel) (stored, ())
                (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference))
              (recoveredSecretOutput problem input) +
              ENNReal.ofReal (4 * Real.sqrt
                ((2 * (2 * orderWidth problem) : Nat) / ((problem.order - 1 : Nat) : ℝ))) := by
  obtain ⟨seed, member, nonidentity, bound⟩ :=
    exists_fixedOffset_selectedExponentRun_bound E fieldTail sameWidth fits odd
      problem nontrivial points addends
  refine ⟨seed, member, nonidentity, ?_⟩
  intro input Reference reference stored
  exact (bound input Reference reference stored).trans
    (add_le_add
      (exponentRecoveryRun_selected_probability_le (p := p) (E := E)
          (Reference := Reference) fieldTail odd problem points nontrivial
        input (AlgorithmRun.pureInput (model := RecoveryModel) (stored, ())
          (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference)))
      le_rfl)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
