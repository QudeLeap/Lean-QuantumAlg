/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.First

/-!
# Actual nearest-plane first-coordinate result

The native dot and norm writes discharge the signed-division input contract.
The actual resulting quotient then drives the three coordinate reductions.
The original integer range and nonzero norm conditions are unchanged.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Complete caller frame outside the actual first-phase writable footprint. -/
def CallerFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.dotProduct.key ∉ other.storageKeys → refs.numerator.key ∉ other.storageKeys →
      refs.normProduct.key ∉ other.storageKeys → refs.denominator.key ∉ other.storageKeys →
        (∀ key ∈ SignedWord.RoundedDiv.mutableKeys refs.division, key ∉ other.storageKeys) →
          refs.reduceProduct.key ∉ other.storageKeys → refs.target.first.key ∉ other.storageKeys →
            refs.target.second.key ∉ other.storageKeys → refs.target.third.key ∉ other.storageKeys →
              after.read other = before.read other

/-- The four actual stages preserve every caller read outside their complete writable footprint. -/
theorem firstInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (firstStep refs store).1 := by
  intro shape other dotProduct numerator normProduct denominator division product first second third
  rw [firstStep_store]
  rw [LatticeArithmetic.pointReduce_callerFrame _ _ _ _ _ other product first second third,
    SignedWord.RoundedDiv.body_callerFrame _ _ other division,
    LatticeNormRefresh.refreshInto_callerFrame _ _ _ other denominator normProduct,
    LatticeDotRefresh.refreshInto_callerFrame _ _ _ _ other numerator dotProduct]

private theorem point_of_frames {before after : Store ctx}
    (refs : LatticeState.PointRefs ctx width) (value : NumberTheory.IntegerPoint3)
    (represents : LatticeArithmetic.PointRawRepresents before refs value)
    (first : after.read (writeInput refs.first) = before.read (writeInput refs.first))
    (second : after.read (writeInput refs.second) = before.read (writeInput refs.second))
    (third : after.read (writeInput refs.third) = before.read (writeInput refs.third)) :
    LatticeArithmetic.PointRawRepresents after refs value := by
  rcases represents with ⟨firstRep, secondRep, thirdRep⟩
  refine ⟨?_, ?_, ?_⟩
  · change RawSignedRepresents (after.read (writeInput refs.first)) value.1
    rw [first]; exact firstRep
  · change RawSignedRepresents (after.read (writeInput refs.second)) value.2.1
    rw [second]; exact secondRep
  · change RawSignedRepresents (after.read (writeInput refs.third)) value.2.2
    rw [third]; exact thirdRep

private theorem division_preserves_point {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    (point : LatticeState.PointRefs ctx width) (value : NumberTheory.IntegerPoint3)
    (represents : LatticeArithmetic.PointRawRepresents store point value)
    (avoids : ∀ key ∈ SignedWord.RoundedDiv.mutableKeys refs.division,
      PointInputAvoidsKey point key) :
    LatticeArithmetic.PointRawRepresents (SignedWord.RoundedDiv.bodyStep refs.division store).1
      point value := by
  apply point_of_frames point value represents
  · exact SignedWord.RoundedDiv.body_callerFrame refs.division store (writeInput point.first)
      (fun key member => (avoids key member).first)
  · exact SignedWord.RoundedDiv.body_callerFrame refs.division store (writeInput point.second)
      (fun key member => (avoids key member).second)
  · exact SignedWord.RoundedDiv.body_callerFrame refs.division store (writeInput point.third)
      (fun key member => (avoids key member).third)

/-- The actual stored coefficient and updated residual satisfy the original nearest-plane target. -/
theorem firstInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (refs : Refs ctx width) (separation : Separation refs) (store : Store ctx)
    (firstValue targetValue : NumberTheory.IntegerPoint3)
    (initial : InitialConditions store refs firstValue targetValue)
    (denominatorNonzero : denominatorValue firstValue ≠ 0) :
    RawSignedRepresents ((firstStep refs store).1.read (writeInput refs.division.output))
        (NumberTheory.nearestIntegerCoefficient (numeratorValue targetValue firstValue)
          (denominatorValue firstValue)) ∧
      LatticeArithmetic.PointRawRepresents (firstStep refs store).1 refs.target
        (targetValue.sub (firstValue.smul (NumberTheory.nearestIntegerCoefficient
          (numeratorValue targetValue firstValue) (denominatorValue firstValue)))) := by
  rw [firstStep_store]
  rcases initial with ⟨firstRep, targetRep, fits⟩
  let dotted := LatticeDotRefresh.refreshStore refs.target refs.basis.first
    (numeratorDotRefs refs) store
  let normed := LatticeNormRefresh.refreshStore refs.basis.first (denominatorNormRefs refs) dotted
  let divided := (SignedWord.RoundedDiv.bodyStep refs.division normed).1
  have dotValues := LatticeDotRefresh.refreshInto_correct refs.target refs.basis.first
    (numeratorDotRefs refs) separation.numeratorDot store targetValue firstValue targetRep firstRep
  have normValues := LatticeNormRefresh.refreshInto_correct refs.basis.first
    (denominatorNormRefs refs)
    separation.denominatorNorm dotted firstValue dotValues.2.2
  have numeratorAfterNorm : RawSignedRepresents (normed.read (writeInput refs.numerator))
      (numeratorValue targetValue firstValue) := by
    rw [LatticeNormRefresh.refreshInto_callerFrame refs.basis.first (denominatorNormRefs refs)
      dotted (writeInput refs.numerator) separation.numeratorAvoidsDenominator
      separation.numeratorAvoidsNormProduct]
    exact dotValues.1
  have targetAfterNorm : LatticeArithmetic.PointRawRepresents normed refs.target targetValue := by
    apply point_of_frames refs.target targetValue dotValues.2.1
    · exact LatticeNormRefresh.refreshInto_callerFrame _ _ dotted (writeInput refs.target.first)
        separation.targetAvoidsDenominator.first separation.targetAvoidsNormProduct.first
    · exact LatticeNormRefresh.refreshInto_callerFrame _ _ dotted (writeInput refs.target.second)
        separation.targetAvoidsDenominator.second separation.targetAvoidsNormProduct.second
    · exact LatticeNormRefresh.refreshInto_callerFrame _ _ dotted (writeInput refs.target.third)
        separation.targetAvoidsDenominator.third separation.targetAvoidsNormProduct.third
  have numeratorAtDivision : RawSignedRepresents (normed.read refs.division.numerator)
      (numeratorValue targetValue firstValue) := by
    rw [refs.divisionNumerator]
    exact numeratorAfterNorm
  have denominatorAtDivision : RawSignedRepresents (normed.read refs.division.denominator)
      (NumberTheory.integerPointSquaredNorm firstValue : Int) := by
    rw [refs.divisionDenominator]
    exact normValues.1
  have denominatorPositive : 0 < NumberTheory.integerPointSquaredNorm firstValue := by
    have nonzero : NumberTheory.integerPointSquaredNorm firstValue ≠ 0 := by
      intro zero
      exact denominatorNonzero (by simp only [denominatorValue, zero, Nat.cast_zero])
    exact Nat.pos_of_ne_zero nonzero
  have coefficient := SignedWord.RoundedDiv.body_outputRepresents_of_raw refs.division
    separation.division normed (numeratorValue targetValue firstValue)
    (NumberTheory.integerPointSquaredNorm firstValue) fits.widthPositive denominatorPositive
    numeratorAtDivision fits.numeratorRange denominatorAtDivision fits.denominatorFits
  have firstAfterDivision := division_preserves_point refs normed refs.basis.first firstValue
    normValues.2 separation.basisFirstAvoidsDivision
  have targetAfterDivision := division_preserves_point refs normed refs.target targetValue
    targetAfterNorm separation.targetAvoidsDivision
  have reduction := LatticeArithmetic.pointReduce_correct (writeInput refs.division.output)
    refs.basis.first refs.target refs.reduceProduct separation.reduction divided
  have targetAfterReduction := reduction.1
    (NumberTheory.nearestIntegerCoefficient (numeratorValue targetValue firstValue)
      (denominatorValue firstValue)) firstValue targetValue coefficient
        firstAfterDivision targetAfterDivision
  have coefficientFrame := reduction.2 (writeInput refs.division.output)
    separation.reduction.first.coefficientAvoidsProduct
    separation.reduction.first.coefficientAvoidsTarget
    separation.reduction.second.coefficientAvoidsTarget
    separation.reduction.third.coefficientAvoidsTarget
  refine ⟨?_, targetAfterReduction⟩
  change RawSignedRepresents ((LatticeArithmetic.pointStore (writeInput refs.division.output)
    refs.basis.first refs.target refs.reduceProduct divided).read
      (writeInput refs.division.output)) _
  rw [coefficientFrame]
  exact coefficient

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst
