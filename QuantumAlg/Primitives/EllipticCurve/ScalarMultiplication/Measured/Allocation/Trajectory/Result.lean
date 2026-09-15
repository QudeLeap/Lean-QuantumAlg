/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Group

/-!
# Exact original two-exponent group expression and complete target columns

The prescribed paired powers yield the original offset multiplied by the
left power and inverse right power. The complete target places the exact
affine result in the original coordinate words, retaining every exponent,
fixed auxiliary coordinate and external reference label with no phase change.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open MeasuredPointAddition

/-- The original paired addends give the exact two-exponent group expression. -/
theorem pairedAffinePath_groupExpression {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {exponentWidth : Nat}
    (points : Fin (2 * exponentWidth) → AffinePoint E) (seed : AffinePoint E)
    (leftBase rightBase : E.GroupPoint)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend exponentWidth leftBase rightBase)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (admissible : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch) :
    (AffineTrajectory.path E points
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
      (List.finRange (2 * exponentWidth)) seed).toGroupPoint =
      seed.toGroupPoint * (leftBase ^ branch.1.val * (rightBase ^ branch.2.val)⁻¹) := by
  rw [pairedAffinePath_toGroupPoint E points seed branch admissible, addends,
    ExceptionalOffsetAveraging.prefixMultiplier_pairedBigEndian]

/-- Every original admissible paired branch has its exact full-reference final affine column. -/
theorem cascadeTarget_pairedAffineInput {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {exponentWidth : Nat}
    (points : Fin (2 * exponentWidth) → AffinePoint E) (seed : AffinePoint E)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (admissible : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch)
    {Reference : Register} (reference : Reference.Index) :
    (cascadeTarget E points Reference (List.finRange (2 * exponentWidth))).applyVec
      (NormalizedVector.ket (initializedReadyBasis p (2 * exponentWidth)
        (pairedAffineInput exponentWidth seed branch), reference)).vec =
      (NormalizedVector.ket (initializedReadyBasis p (2 * exponentWidth)
        (pairedAffineInput exponentWidth
          (AffineTrajectory.path E points
            (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
            (List.finRange (2 * exponentWidth)) seed) branch), reference)).vec := by
  exact cascadeTarget_initialized_affine E points
    (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
    (pairedExponentInput p exponentWidth branch)
    (pairedExponentInput_rangeBasis p exponentWidth branch)
    (List.finRange (2 * exponentWidth)) seed
    (AffineTrajectory.admissible_finRange_of_group E points _ seed admissible) reference

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
