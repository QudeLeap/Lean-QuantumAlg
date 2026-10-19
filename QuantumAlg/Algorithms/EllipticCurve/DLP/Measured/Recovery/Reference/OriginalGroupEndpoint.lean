/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Effects
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Trajectory.Prefix

/-!
# Original good affine endpoint equals the original full group oracle

The same paired big-endian schedule and the same original admissible branch
end at the original group-oracle value. This is a mathematical coordinate
identity; it neither postselects a branch nor adds an algorithm premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace OriginalGroupEndpoint

noncomputable section

open QuantumAlg QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.FiniteCyclicDLP ScalarMultiplication

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The original good set identifies the actual affine endpoint with the full group label. -/
lemma affinePath_eq_idealGroupOutput (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (branch : (ECDLP.Measured.idealBranchRegister problem).Index)
    (good : ExceptionalOffsetAveraging.Admissible (2 * orderWidth problem)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem))
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch) :
    (AffineTrajectory.path E points
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) branch)
      (List.finRange (2 * orderWidth problem)) seed).toGroupPoint =
      ECDLP.Measured.idealGroupOutput problem seed branch := by
  change Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem) at branch
  have endpoint := AffineTrajectory.pointPrefix_toGroupPoint E points
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) branch)
    seed good (2 * orderWidth problem) le_rfl
  unfold AffineTrajectory.pointPrefix at endpoint
  rw [List.take_of_length_le (Nat.le_of_eq List.length_finRange)] at endpoint
  change _ = seed.toGroupPoint *
    ExceptionalOffsetAveraging.prefixMultiplier (2 * orderWidth problem)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem))
      (fun index => (points index).toGroupPoint) branch (2 * orderWidth problem) at endpoint
  rw [addends, ExceptionalOffsetAveraging.prefixMultiplier_pairedBigEndian] at endpoint
  exact endpoint

end

end OriginalGroupEndpoint
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
