/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.PreparedSupport
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Effects
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Result

/-!
# Exact group labels on admissible affine paths

Admissible source branches have finite affine outputs, and those
outputs are exactly the original full-group oracle values. The affine domain
is derived from the actual good path; no extra nonidentity assumption is
imposed on the mathematical ideal oracle or its padded inputs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open GenericPointAddition.InPlace FiniteCyclicDLP

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

/-- Every original good affine path has exactly the literal full-group ideal output. -/
lemma preparedGoodPath_groupOutput (problem : KnownOrderProblem E.GroupPoint)
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
lemma preparedGoodPath_nonidentity (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (branch : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem))
    (good : branch ∈ preparedAdmissibleBranches problem points seed) :
    idealGroupOutput problem seed branch ≠ 1 := by
  rw [← preparedGoodPath_groupOutput problem points seed addends branch good]
  exact PointSemantics.toGroupPoint_ne_one _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
