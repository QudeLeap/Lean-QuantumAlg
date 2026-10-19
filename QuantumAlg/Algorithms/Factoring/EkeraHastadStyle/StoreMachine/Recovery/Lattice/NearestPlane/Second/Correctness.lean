/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second

/-!
# Actual second-coordinate nearest-plane correctness

The five actual metrics establish the unchanged signed-division input contract.
The resulting actual quotient drives the target update and equals the original
public second nearest-plane coefficient, with the original range premises.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def divisionCells : List PhaseCell :=
  [.divisionMagnitude, .divisionNegative, .divisionWideNumerator,
    .divisionWideDenominator, .divisionQuotientRemainder, .divisionOutput]

private lemma division_frame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (store : Store ctx) {shape : CShape} (other : CWriteRef ctx shape) (source : PhaseCell)
    (sourceKey : other.key = phaseCellKey refs source) (outside : source ∉ divisionCells) :
    (RoundedDiv.bodyStep refs.division store).1.read (.storage other.toCStorageRef) =
      store.read (.storage other.toCStorageRef) := by
  apply RoundedDiv.body_callerFrame
  intro key present
  have keys : RoundedDiv.mutableKeys refs.division = divisionCells.map (phaseCellKey refs) := rfl
  rw [keys] at present
  obtain ⟨cell, cellMember, keyEq⟩ := List.mem_map.mp present
  subst key
  change phaseCellKey refs cell ∉ [other.key]
  simpa only [List.mem_singleton, sourceKey] using
    separation.phaseCellKey_ne cell source (fun equal => outside (equal ▸ cellMember))

private lemma point_of_frames {before after : Store ctx}
    (refs : LatticeState.PointRefs ctx width) (value : NumberTheory.IntegerPoint3)
    (rep : LatticeArithmetic.PointRawRepresents before refs value)
    (first : after.read (writeInput refs.first) = before.read (writeInput refs.first))
    (second : after.read (writeInput refs.second) = before.read (writeInput refs.second))
    (third : after.read (writeInput refs.third) = before.read (writeInput refs.third)) :
    LatticeArithmetic.PointRawRepresents after refs value := by
  refine ⟨?_, ?_, ?_⟩
  · rw [first]; exact rep.1
  · rw [second]; exact rep.2.1
  · rw [third]; exact rep.2.2

/-- The actual stored coefficient and residual satisfy the original second-phase contract. -/
lemma secondInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3) (target : NumberTheory.IntegerPoint3)
    (initial : Initial store refs basis target) (fits : Fits width basis target) :
    RawSignedRepresents ((secondStep refs store).1.read (writeInput refs.division.output))
        (basis.nearestPlaneSecondCoefficient target) ∧
      LatticeArithmetic.PointRawRepresents (secondStep refs store).1 refs.target
        (LatticeNearestPlaneResidual.afterSecond basis target) := by
  rw [secondStep_store]
  rcases initial with ⟨firstRep, secondRep, targetRep⟩
  let residual := LatticeNearestPlaneResidual.afterThird basis target
  let metricState := secondPrefixStore refs store
  let numerated := numeratorStore refs metricState
  let divided := (RoundedDiv.bodyStep refs.division numerated).1
  have prefixResult := secondPrefixInto_correct refs separation store
    basis.first basis.second residual firstRep secondRep targetRep
  have numeratorResult := numeratorInto_correct refs separation.phase metricState
    (NumberTheory.integerPointDot basis.first basis.first)
    (NumberTheory.integerPointDot basis.second basis.first)
    (NumberTheory.integerPointDot residual basis.second)
    (NumberTheory.integerPointDot residual basis.first)
    (prefixResult.2 .g11) (prefixResult.2 .g21)
    (prefixResult.2 .targetSecond) (prefixResult.2 .targetFirst)
  have numeratorRep : RawSignedRepresents (numerated.read refs.division.numerator)
      (LatticeNearestPlaneResidual.secondNumerator basis residual) := by
    rw [refs.divisionNumerator]
    simpa only [LatticeNearestPlaneResidual.secondNumerator,
      NumberTheory.integerPointDot_self] using numeratorResult
  let denominator := NumberTheory.integerPointAreaSquared basis.first basis.second
  have denominatorRep : RawSignedRepresents (numerated.read refs.division.denominator)
      (denominator : Int) := by
    rw [refs.divisionDenominator,
      numeratorInto_frame refs separation.phase metricState refs.denominator .denominator rfl
        (by decide) (by decide)]
    have represented := prefixResult.2 .denominator
    change RawSignedRepresents (metricState.read (writeInput refs.denominator))
      (NumberTheory.integerPointDot (NumberTheory.integerPointCross basis.first basis.second)
        (NumberTheory.integerPointCross basis.first basis.second)) at represented
    rw [NumberTheory.integerPointDot_self] at represented
    exact represented
  have positive : 0 < denominator := by
    have bound := fits.denominatorPositive
    change (0 : Int) < (denominator : Int) at bound
    exact_mod_cast bound
  have bounded : denominator < CShape.wordModulus width := by
    simpa only [NumberTheory.IntegerBasis3.secondReductionDenominator, Int.natAbs_natCast] using
      fits.denominatorFits
  have coefficient := RoundedDiv.body_outputRepresents_of_raw refs.division separation.division
    numerated (LatticeNearestPlaneResidual.secondNumerator basis residual) denominator
    fits.widthPositive positive numeratorRep fits.numeratorRange denominatorRep bounded
  change RawSignedRepresents (divided.read (writeInput refs.division.output))
    (NumberTheory.nearestIntegerCoefficient
      (LatticeNearestPlaneResidual.secondNumerator basis
        (LatticeNearestPlaneResidual.afterThird basis target)) basis.secondReductionDenominator)
    at coefficient
  rw [LatticeNearestPlaneResidual.nearestIntegerCoefficient_secondResidual] at coefficient
  have preserved {shape : CShape} (other : CWriteRef ctx shape) (source : PhaseCell)
      (key : other.key = phaseCellKey refs source) (outside : source ∉ divisionCells)
      (notNumerator : .numerator ≠ source) (notProduct : .numeratorProduct ≠ source) :
      divided.read (.storage other.toCStorageRef) =
        metricState.read (.storage other.toCStorageRef) := by
    rw [division_frame refs separation.phase numerated other source key outside,
      numeratorInto_frame refs separation.phase metricState other source key
        notNumerator notProduct]
  have secondAfterDivision : LatticeArithmetic.PointRawRepresents divided refs.basis.second
      basis.second := by
    apply point_of_frames refs.basis.second basis.second (prefixResult.1 .second)
    · exact preserved refs.basis.second.first .basisSecondFirst rfl
        (by decide) (by decide) (by decide)
    · exact preserved refs.basis.second.second .basisSecondSecond rfl
        (by decide) (by decide) (by decide)
    · exact preserved refs.basis.second.third .basisSecondThird rfl
        (by decide) (by decide) (by decide)
  have targetAfterDivision : LatticeArithmetic.PointRawRepresents divided refs.target residual := by
    apply point_of_frames refs.target residual (prefixResult.1 .target)
    · exact preserved refs.target.first .targetFirst rfl
        (by decide) (by decide) (by decide)
    · exact preserved refs.target.second .targetSecond rfl
        (by decide) (by decide) (by decide)
    · exact preserved refs.target.third .targetThird rfl
        (by decide) (by decide) (by decide)
  have reduction := LatticeArithmetic.pointReduce_correct (writeInput refs.division.output)
    refs.basis.second refs.target refs.reduceProduct separation.reduction divided
  have targetAfterReduction := reduction.1 (basis.nearestPlaneSecondCoefficient target)
    basis.second residual coefficient secondAfterDivision targetAfterDivision
  have coefficientFrame := reduction.2 (writeInput refs.division.output)
    separation.reduction.first.coefficientAvoidsProduct
    separation.reduction.first.coefficientAvoidsTarget
    separation.reduction.second.coefficientAvoidsTarget
    separation.reduction.third.coefficientAvoidsTarget
  refine ⟨?_, targetAfterReduction⟩
  change RawSignedRepresents ((LatticeArithmetic.pointStore (writeInput refs.division.output)
    refs.basis.second refs.target refs.reduceProduct divided).read
      (writeInput refs.division.output)) _
  rw [coefficientFrame]
  exact coefficient

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
