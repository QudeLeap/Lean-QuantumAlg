/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Target
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Ideal

/-!
# Exact original group labels on the actual good output

Original admissible source branches have finite affine outputs, and those
outputs are exactly the original full-group oracle values. The affine domain
is derived from the actual good path; no extra nonidentity assumption is
imposed on the mathematical ideal oracle or its padded inputs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding
open GenericPointAddition.InPlace FiniteCyclicDLP

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

/-- Every original good affine path has exactly the literal full-group ideal output. -/
theorem preparedGoodPath_groupOutput (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (branch : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem))
    (good : branch ∈ preparedAdmissibleBranches problem points seed) :
    (ScalarMultiplication.AffineTrajectory.path E points
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) branch)
      (List.finRange (2 * orderWidth problem)) seed).toGroupPoint =
        idealGroupOutput problem seed branch := by
  classical
  exact pairedAffinePath_groupExpression E points seed problem.generator problem.target
    addends branch (Finset.mem_filter.mp good).2

/-- Nonidentity of a good ideal output follows from its actual affine path. -/
theorem preparedGoodPath_nonidentity (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (branch : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem))
    (good : branch ∈ preparedAdmissibleBranches problem points seed) :
    idealGroupOutput problem seed branch ≠ 1 := by
  rw [← preparedGoodPath_groupOutput problem points seed addends branch good]
  exact PointSemantics.toGroupPoint_ne_one _

/-- The actual allocated good column and the ideal group label refer to the same affine output. -/
theorem placedConvertedTarget_goodBranch_group (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (branch : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem))
    (good : branch ∈ preparedAdmissibleBranches problem points seed)
    {Reference : Register} (reference : Reference.Index) :
    ∃ final : AffinePoint E,
      final.toGroupPoint = idealGroupOutput problem seed branch ∧
      (placedConvertedTarget E points (List.finRange (2 * orderWidth problem))
        (Semantics.radixUnit p fieldTail.succ odd) Reference).applyVec
          (NormalizedVector.ket (initializedOutputEmbedding p (2 * orderWidth problem) Reference
            (pairedMontgomeryInput fieldTail (orderWidth problem) sameWidth fits seed branch,
              reference))).vec =
        (NormalizedVector.ket (initializedOutputEmbedding p (2 * orderWidth problem) Reference
          (pairedMontgomeryInput fieldTail (orderWidth problem) sameWidth fits final branch,
            reference))).vec := by
  classical
  refine ⟨ScalarMultiplication.AffineTrajectory.path E points
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) branch)
    (List.finRange (2 * orderWidth problem)) seed,
    preparedGoodPath_groupOutput problem points seed addends branch good, ?_⟩
  exact placedConvertedTarget_pairedMontgomery E fieldTail sameWidth fits odd points seed branch
    (Finset.mem_filter.mp good).2 reference

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
