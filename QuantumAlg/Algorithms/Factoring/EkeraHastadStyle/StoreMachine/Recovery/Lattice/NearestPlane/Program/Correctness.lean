/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Program.Preservation

/-!
# Complete actual nearest-plane correctness

The chronological third, second and first reductions produce the original
public coefficient center and residual. Every retained coefficient is read
from the final actual store, after both later reductions have finished.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Original basis and target representations, without initial scratch-value conditions. -/
structure Initial (refs : Refs ctx width) (store : Store ctx)
    (basis : NumberTheory.IntegerBasis3) (target : NumberTheory.IntegerPoint3) : Prop where
  first : LatticeArithmetic.PointRawRepresents store refs.basis.first basis.first
  second : LatticeArithmetic.PointRawRepresents store refs.basis.second basis.second
  third : LatticeArithmetic.PointRawRepresents store refs.basis.third basis.third
  target : LatticeArithmetic.PointRawRepresents store refs.target target

/-- All three public coefficients and the complete residual are represented in the final store. -/
def Result (refs : Refs ctx width) (store : Store ctx)
    (basis : NumberTheory.IntegerBasis3) (target : NumberTheory.IntegerPoint3) : Prop :=
  RawSignedRepresents (store.read (writeInput refs.third.division.output))
      (basis.nearestPlaneThirdCoefficient target) ∧
    RawSignedRepresents (store.read (writeInput refs.second.division.output))
      (basis.nearestPlaneSecondCoefficient target) ∧
    RawSignedRepresents (store.read (writeInput refs.first.division.output))
      (basis.nearestPlaneFirstCoefficient target) ∧
    LatticeArithmetic.PointRawRepresents store refs.target
      (target.sub (basis.linearCombination (basis.nearestPlaneCoefficientCenter target)))

/-- Actual three-stage execution computes the original coefficient center and target residual. -/
theorem threeInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3) (target : NumberTheory.IntegerPoint3)
    (initial : Initial refs store basis target) (fits : Fits width basis target) :
    Result refs (threeStep refs store).1 basis target := by
  let afterThird := (LatticeNearestPlaneThird.thirdStep (thirdRefs refs) store).1
  let afterSecond := (LatticeNearestPlaneSecond.secondStep (secondRefs refs) afterThird).1
  have thirdResult := LatticeNearestPlaneThird.thirdInto_basis_correct (thirdRefs refs)
    separation.third store basis target fits.third initial.first initial.second initial.third
    initial.target
  have firstAtSecond := thirdInto_preserves_basis_first refs separation store basis.first
    initial.first
  have secondAtSecond := thirdInto_preserves_basis_second refs separation store basis.second
    initial.second
  have secondResult := LatticeNearestPlaneSecond.secondInto_correct (secondRefs refs)
    separation.second afterThird basis target ⟨firstAtSecond, secondAtSecond, thirdResult.2⟩
    fits.second
  have firstAtFirst := secondInto_preserves_basis_first refs separation afterThird basis.first
    firstAtSecond
  have firstResult := LatticeNearestPlaneFirst.firstInto_correct (firstRefs refs)
    separation.first afterSecond basis.first (LatticeNearestPlaneResidual.afterSecond basis target)
    ⟨firstAtFirst, secondResult.2, fits.first⟩ fits.firstDenominatorNonzero
  simp only [LatticeNearestPlaneFirst.numeratorValue, LatticeNearestPlaneFirst.denominatorValue,
    LatticeNearestPlaneResidual.nearestIntegerCoefficient_firstResidual,
    LatticeNearestPlaneResidual.afterFirst_eq_sub_linearCombination] at firstResult
  refine ⟨?_, ?_, firstResult.1, firstResult.2⟩
  · change RawSignedRepresents
      ((LatticeNearestPlaneFirst.firstStep (firstRefs refs) afterSecond).1.read
        (writeInput refs.third.division.output)) _
    rw [firstInto_callerFrame refs afterSecond _ separation.firstPreservesThirdOutput]
    change RawSignedRepresents
      ((LatticeNearestPlaneSecond.secondStep (secondRefs refs) afterThird).1.read
        (writeInput refs.third.division.output)) _
    rw [secondInto_callerFrame refs afterThird _ separation.secondPreservesThirdOutput]
    exact thirdResult.1
  · change RawSignedRepresents
      ((LatticeNearestPlaneFirst.firstStep (firstRefs refs) afterSecond).1.read
        (writeInput refs.second.division.output)) _
    rw [firstInto_callerFrame refs afterSecond _ separation.firstPreservesSecondOutput]
    exact secondResult.1

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThree
