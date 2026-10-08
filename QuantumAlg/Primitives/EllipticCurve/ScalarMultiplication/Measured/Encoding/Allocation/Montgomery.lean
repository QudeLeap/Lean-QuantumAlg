/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Allocation.Trajectory
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Montgomery
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Result

/-!
# Actual converted scalar execution on the original Montgomery good set

The caller supplies the original two exponent words and Montgomery affine
seed coordinates. The original active-step exclusions establish the actual
converted circuit's full-density domain. No converted-density or allocated
workspace premise is required.

The complete target column returns the original Montgomery encoding of the
affine path, retaining every exponent, initialized work coordinate and external
reference without a phase change. The same final affine point denotes the
original offset times the left power and inverse right power.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open Execution MeasuredUncompute MeasuredPointAddition Allocation
open GenericPointAddition.InPlace

/-- Original paired exponents and the original Montgomery affine seed form the supplied input. -/
def pairedMontgomeryInput {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (fieldTail exponentWidth : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth)) :
    (before p.size (2 * exponentWidth)).register.Index :=
  montgomeryInput fieldTail (2 * exponentWidth) sameWidth fits
    (pairedExponentInput p exponentWidth branch) seed.x seed.y

/-- The original good set constrains only supplied Montgomery input and group values. -/
def pairedMontgomeryAllowed {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) {exponentWidth : Nat}
    (points : Fin (2 * exponentWidth) → AffinePoint E) (seed : AffinePoint E)
    (input : (before p.size (2 * exponentWidth)).register.Index) : Prop :=
  ∃ branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth),
    input = pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed branch ∧
      ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
        (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
        (fun index => (points index).toGroupPoint) seed.toGroupPoint branch

/-- The original group condition establishes the Montgomery input trajectory. -/
theorem pairedMontgomeryInput_convertedTrajectory {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    {exponentWidth : Nat} (points : Fin (2 * exponentWidth) → AffinePoint E)
    (seed : AffinePoint E) (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (admissible : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch) :
    convertedInputTrajectory E points (List.finRange (2 * exponentWidth))
      (Semantics.radixUnit p fieldTail.succ odd)
      (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed branch) := by
  refine ⟨pairedExponentInput p exponentWidth branch, seed, ?_,
    pairedAffineInput_trajectory E points seed branch admissible⟩
  unfold pairedMontgomeryInput
  rw [montgomeryInput_fieldWords fieldTail (2 * exponentWidth) sameWidth fits,
    Semantics.radixUnit_coe]

/-- Actual initialized converted execution has its full density on the original good set. -/
theorem convertedCircuit_density_of_pairedMontgomery_admissible {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    {exponentWidth : Nat} (points : Fin (2 * exponentWidth) → AffinePoint E)
    (seed : AffinePoint E) {Reference : Register} {H : Type} [Fintype H]
    (original : State (before p.size (2 * exponentWidth)) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : ∀ input,
      ¬pairedMontgomeryAllowed E fieldTail sameWidth fits points seed input.1 →
        original.quantumMarginal.matrix input input = 0) :
    ((convertedCircuit E points (List.finRange (2 * exponentWidth))
      (Semantics.radixUnit p fieldTail.succ odd)).execute Reference original).quantumMarginal =
      convertedResultDensity E points (List.finRange (2 * exponentWidth))
        (Semantics.radixUnit p fieldTail.succ odd) Reference original.quantumMarginal := by
  apply convertedCircuit_density_of_input_trajectory
  intro input outside
  apply support input
  rintro ⟨branch, same, admissible⟩
  apply outside
  rw [same]
  exact pairedMontgomeryInput_convertedTrajectory E fieldTail sameWidth fits odd
    points seed branch admissible

/-- Every original good branch returns its exact Montgomery affine path and retained bits. -/
theorem convertedCascadeTarget_pairedMontgomeryInput {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    {exponentWidth : Nat} (points : Fin (2 * exponentWidth) → AffinePoint E)
    (seed : AffinePoint E) (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (admissible : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch)
    {Reference : Register} (reference : Reference.Index) :
    (convertedCascadeTarget E points (List.finRange (2 * exponentWidth))
      (Semantics.radixUnit p fieldTail.succ odd) Reference).applyVec
        (NormalizedVector.ket (initializedReadyBasis p (2 * exponentWidth)
          (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed branch),
          reference)).vec =
      (NormalizedVector.ket (initializedReadyBasis p (2 * exponentWidth)
        (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits
          (AffineTrajectory.path E points
            (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
            (List.finRange (2 * exponentWidth)) seed) branch), reference)).vec := by
  have before := pairOperator_fromMontgomery fieldTail (2 * exponentWidth) sameWidth fits odd
    (pairedExponentInput p exponentWidth branch) seed.x seed.y reference
  have middle := cascadeTarget_pairedAffineInput E points seed branch admissible reference
  have after := pairOperator_toMontgomery fieldTail (2 * exponentWidth) sameWidth fits odd
    (pairedExponentInput p exponentWidth branch)
    (AffineTrajectory.path E points
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
      (List.finRange (2 * exponentWidth)) seed).x
    (AffineTrajectory.path E points
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
      (List.finRange (2 * exponentWidth)) seed).y reference
  have joined := (congrArg
    (fun vector => (pairOperator p.size (2 * exponentWidth) (InPlaceTarget.modulusWord p)
      (Semantics.radixUnit p fieldTail.succ odd) Reference).applyVec
        ((cascadeTarget E points Reference (List.finRange (2 * exponentWidth))).applyVec vector))
    before).trans ((congrArg
      (pairOperator p.size (2 * exponentWidth) (InPlaceTarget.modulusWord p)
        (Semantics.radixUnit p fieldTail.succ odd) Reference).applyVec middle).trans after)
  rw [convertedCascadeTarget, UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec]
  exact joined

/-- The same full Montgomery target column denotes the original two-exponent group expression. -/
theorem convertedCascadeTarget_pairedMontgomery_group {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    {exponentWidth : Nat} (points : Fin (2 * exponentWidth) → AffinePoint E)
    (seed : AffinePoint E) (leftBase rightBase : E.GroupPoint)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend exponentWidth leftBase rightBase)
    (branch : Fin (2 ^ exponentWidth) × Fin (2 ^ exponentWidth))
    (admissible : ExceptionalOffsetAveraging.Admissible (2 * exponentWidth)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth)
      (fun index => (points index).toGroupPoint) seed.toGroupPoint branch)
    {Reference : Register} (reference : Reference.Index) :
    ∃ final : AffinePoint E,
      final.toGroupPoint =
        seed.toGroupPoint * (leftBase ^ branch.1.val * (rightBase ^ branch.2.val)⁻¹) ∧
      (convertedCascadeTarget E points (List.finRange (2 * exponentWidth))
        (Semantics.radixUnit p fieldTail.succ odd) Reference).applyVec
          (NormalizedVector.ket (initializedReadyBasis p (2 * exponentWidth)
            (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits seed branch),
            reference)).vec =
        (NormalizedVector.ket (initializedReadyBasis p (2 * exponentWidth)
          (pairedMontgomeryInput fieldTail exponentWidth sameWidth fits final branch),
          reference)).vec := by
  refine ⟨AffineTrajectory.path E points
    (ExceptionalOffsetAveraging.pairedBigEndianSelected exponentWidth branch)
    (List.finRange (2 * exponentWidth)) seed,
    pairedAffinePath_groupExpression E points seed leftBase rightBase addends branch admissible, ?_⟩
  exact convertedCascadeTarget_pairedMontgomeryInput E fieldTail sameWidth fits odd
    points seed branch admissible reference

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
