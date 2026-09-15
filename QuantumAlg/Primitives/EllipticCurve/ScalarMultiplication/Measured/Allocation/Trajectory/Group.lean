/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Action
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Exponents
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Trajectory.Prefix

/-!
# Actual initialized scalar execution on the original paired good set

The supplied input consists of the original two exponent words and an affine
seed. The original exceptional-offset condition implies every measured
step's domain. Full-density correctness follows for coherent inputs supported
on this original good set, including arbitrary reference correlations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution MeasuredPointAddition

/-- The original paired exponent words and affine seed supply the complete caller input. -/
def pairedAffineInput {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (exponentWidth : Nat) (seed : AffinePoint E)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    (before p.size (2 * exponentWidth)).register.Index :=
  inputLabel p.size (2 * exponentWidth) (pairedExponentInput p exponentWidth branch)
    (fieldWord seed.x) (fieldWord seed.y)

/-- The original good set is stated entirely on supplied branch and group values. -/
def pairedInputAllowed {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {exponentWidth : Nat} (points : Fin (2 * exponentWidth) → AffinePoint E)
    (seed : AffinePoint E) (input : (before p.size (2 * exponentWidth)).register.Index) : Prop :=
  ∃ branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth),
    input = pairedAffineInput exponentWidth seed branch ∧
      ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
        (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
        (fun index => (points index).toGroupPoint) seed.toGroupPoint branch

/-- Every original admissible paired branch satisfies the complete initialized trajectory domain. -/
theorem pairedAffineInput_trajectory {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {exponentWidth : Nat}
    (points : Fin (2 * exponentWidth) → AffinePoint E) (seed : AffinePoint E)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (admissible : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch) :
    inputTrajectory E points (List.finRange (2 * exponentWidth))
      (pairedAffineInput exponentWidth seed branch) := by
  apply inputTrajectory_of_affine E points
    (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
    (pairedExponentInput p exponentWidth branch)
    (pairedExponentInput_rangeBasis p exponentWidth branch)
  exact AffineTrajectory.admissible_finRange_of_group E points _ seed admissible

/-- Actual complete execution has the full independent density on the original paired good set. -/
theorem circuit_density_of_paired_admissible {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {exponentWidth : Nat}
    (points : Fin (2 * exponentWidth) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (before p.size (2 * exponentWidth)) Reference H)
    (support : ∀ input,
      ¬pairedInputAllowed E points seed input.1 →
        original.quantumMarginal.matrix input input = 0) :
    ((circuit E points (List.finRange (2 * exponentWidth))).execute Reference
      original).quantumMarginal =
      resultDensity E points (List.finRange (2 * exponentWidth)) Reference
        original.quantumMarginal := by
  apply circuit_density_of_input_trajectory
  intro input outside
  apply support input
  rintro ⟨branch, same, admissible⟩
  apply outside
  rw [same]
  exact pairedAffineInput_trajectory E points seed branch admissible

/-- The final affine point denotes the original offset times the selected group product. -/
theorem pairedAffinePath_toGroupPoint {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {exponentWidth : Nat}
    (points : Fin (2 * exponentWidth) → AffinePoint E) (seed : AffinePoint E)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (admissible : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch) :
    (AffineTrajectory.path E points
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
      (List.finRange (2 * exponentWidth)) seed).toGroupPoint =
      seed.toGroupPoint * ExceptionalOffsetAveraging.prefixMultiplier (2 * exponentWidth)
        (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
        (fun index => (points index).toGroupPoint) branch (2 * exponentWidth) := by
  have good : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (fun (_ : Unit) index =>
        ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch index)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint () := by
    exact admissible
  have result := AffineTrajectory.pointPrefix_toGroupPoint E points
    (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch) seed good
    (2 * exponentWidth) le_rfl
  simpa only [AffineTrajectory.pointPrefix,
    List.take_of_length_le (Nat.le_of_eq List.length_finRange),
    ExceptionalOffsetAveraging.prefixMultiplier] using result

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
