/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Frame

/-!
# Actual third-coordinate nearest-plane correctness

The normalized actual inputs discharge the original signed-division domain.
The actual resulting coefficient drives the third-direction residual update;
no scratch initialization is assumed.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual normalization, division and reduction compute the original signed coefficient. -/
theorem thirdNormalizeInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (numerator denominator : Int)
    (third target : NumberTheory.IntegerPoint3) (fits : NormalizeFits width numerator denominator)
    (numeratorRep : RawSignedRepresents (store.read (writeInput refs.numerator)) numerator)
    (denominatorRep : RawSignedRepresents (store.read (writeInput refs.denominator)) denominator)
    (thirdRep : LatticeArithmetic.PointRawRepresents store refs.basis.third third)
    (targetRep : LatticeArithmetic.PointRawRepresents store refs.target target) :
    RawSignedRepresents ((thirdNormalizeStep refs store).1.read (writeInput refs.division.output))
        (NumberTheory.nearestIntegerCoefficient numerator denominator) ∧
      LatticeArithmetic.PointRawRepresents (thirdNormalizeStep refs store).1 refs.target
        (target.sub
          (third.smul (NumberTheory.nearestIntegerCoefficient numerator denominator))) := by
  let prepared := signedInputsStore refs store
  let divided := (RoundedDiv.bodyStep refs.division prepared).1
  have inputs := signedInputsStore_correct refs separation.phase store numerator denominator
    fits numeratorRep denominatorRep
  have positive : 0 < denominator.natAbs := by
    apply Nat.pos_of_ne_zero
    exact fun zero => fits.denominatorNonzero (Int.natAbs_eq_zero.mp zero)
  have coefficient := RoundedDiv.body_outputRepresents_of_raw refs.division separation.division
    prepared (if denominator < 0 then -numerator else numerator) denominator.natAbs
    fits.widthPositive positive inputs.1 fits.numeratorFits inputs.2 fits.denominatorMagnitudeFits
  rw [nearestIntegerCoefficient_sign_normalize_denominator] at coefficient
  have thirdAfterDivision :
      LatticeArithmetic.PointRawRepresents divided refs.basis.third third := by
    apply point_of_frames refs.basis.third third thirdRep
    · exact beforeReduction_namedFrame refs separation.phase store
        refs.basis.third.first .basisThirdFirst rfl (by decide)
    · exact beforeReduction_namedFrame refs separation.phase store
        refs.basis.third.second .basisThirdSecond rfl (by decide)
    · exact beforeReduction_namedFrame refs separation.phase store
        refs.basis.third.third .basisThirdThird rfl (by decide)
  have targetAfterDivision : LatticeArithmetic.PointRawRepresents divided refs.target target := by
    apply point_of_frames refs.target target targetRep
    · exact beforeReduction_namedFrame refs separation.phase store
        refs.target.first .targetFirst rfl (by decide)
    · exact beforeReduction_namedFrame refs separation.phase store
        refs.target.second .targetSecond rfl (by decide)
    · exact beforeReduction_namedFrame refs separation.phase store
        refs.target.third .targetThird rfl (by decide)
  have reduction := LatticeArithmetic.pointReduce_correct (writeInput refs.division.output)
    refs.basis.third refs.target refs.reduceProduct separation.reduction divided
  have targetAfterReduction := reduction.1
    (NumberTheory.nearestIntegerCoefficient numerator denominator) third target
    coefficient thirdAfterDivision targetAfterDivision
  have coefficientFrame := reduction.2 (writeInput refs.division.output)
    separation.reduction.first.coefficientAvoidsProduct
    separation.reduction.first.coefficientAvoidsTarget
    separation.reduction.second.coefficientAvoidsTarget
    separation.reduction.third.coefficientAvoidsTarget
  refine ⟨?_, targetAfterReduction⟩
  change RawSignedRepresents ((LatticeArithmetic.pointStore (writeInput refs.division.output)
    refs.basis.third refs.target refs.reduceProduct divided).read
      (writeInput refs.division.output)) _
  rw [coefficientFrame]
  exact coefficient

/-- The actual full phase computes the original determinant-quotient coefficient and residual. -/
theorem thirdInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (first second third target : NumberTheory.IntegerPoint3)
    (fits : Fits width first second third target)
    (firstRep : LatticeArithmetic.PointRawRepresents store refs.basis.first first)
    (secondRep : LatticeArithmetic.PointRawRepresents store refs.basis.second second)
    (thirdRep : LatticeArithmetic.PointRawRepresents store refs.basis.third third)
    (targetRep : LatticeArithmetic.PointRawRepresents store refs.target target) :
    RawSignedRepresents ((thirdStep refs store).1.read (writeInput refs.division.output))
        (NumberTheory.nearestIntegerCoefficient (numeratorValue first second target)
          (denominatorValue first second third)) ∧
      LatticeArithmetic.PointRawRepresents (thirdStep refs store).1 refs.target
        (target.sub (third.smul (NumberTheory.nearestIntegerCoefficient
          (numeratorValue first second target) (denominatorValue first second third)))) := by
  have metrics := thirdMetricPrefixInto_correct refs separation store first second third target
    firstRep secondRep thirdRep targetRep
  exact thirdNormalizeInto_correct refs separation (metricPrefixStore refs store)
    (numeratorValue first second target) (denominatorValue first second third) third target fits
    metrics.1 metrics.2.1 metrics.2.2.2.2.1 metrics.2.2.2.2.2.1

/-- Specializing the actual circuit to a basis gives the public third nearest-plane coefficient. -/
theorem thirdInto_basis_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3) (target : NumberTheory.IntegerPoint3)
    (fits : Fits width basis.first basis.second basis.third target)
    (firstRep : LatticeArithmetic.PointRawRepresents store refs.basis.first basis.first)
    (secondRep : LatticeArithmetic.PointRawRepresents store refs.basis.second basis.second)
    (thirdRep : LatticeArithmetic.PointRawRepresents store refs.basis.third basis.third)
    (targetRep : LatticeArithmetic.PointRawRepresents store refs.target target) :
    RawSignedRepresents ((thirdStep refs store).1.read (writeInput refs.division.output))
        (basis.nearestPlaneThirdCoefficient target) ∧
      LatticeArithmetic.PointRawRepresents (thirdStep refs store).1 refs.target
        (LatticeNearestPlaneResidual.afterThird basis target) := by
  have result := thirdInto_correct refs separation store basis.first basis.second basis.third
    target fits firstRep secondRep thirdRep targetRep
  simpa only [numeratorValue, denominatorValue, crossValue,
    LatticeNearestPlaneResidual.nearestIntegerCoefficient_third,
    LatticeNearestPlaneResidual.afterThird] using result

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
