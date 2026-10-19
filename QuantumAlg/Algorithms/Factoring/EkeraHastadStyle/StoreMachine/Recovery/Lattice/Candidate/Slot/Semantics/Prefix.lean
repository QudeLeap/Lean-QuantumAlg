/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Outcome

/-!
# Source facts after actual candidate-distance and near-target execution
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotSemantics

open Execution
open ClassicalRoutines.NumberTheory.SignedWord hiding writeInput
open LatticeCandidateSlotFrames
open LatticeCandidateSlotMachine (writeInput)
open LatticeCandidateSlotOutcome (initialConditions_transport)

noncomputable section

/-- The actual caller store after the original distance and near-target stages. -/
def distanceScaleStore {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {coordinateWidth modulusWidth : Nat} (offset : NumberTheory.IntegerPoint3)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (store : Store ctx) : Store ctx :=
  (LatticeNearTargetScale.scaleStep (model := model) refs.nearTarget
    (LatticeCandidateDistancePrefix.prefixStep (model := model)
      offset refs.distance store).1).1

/-- All caller reads outside the original two-stage footprint survive actual execution. -/
lemma distanceScaleStore_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {coordinateWidth modulusWidth : Nat} (offset : NumberTheory.IntegerPoint3)
    (refs : LatticeCandidateSlotMachine.Refs ctx coordinateWidth modulusWidth)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (distance : AvoidsStageWrites refs other .distance)
    (near : AvoidsStageWrites refs other .near) :
    (distanceScaleStore (model := model) offset refs store).read other = store.read other :=
  (scaleInto_callerFrame refs _ other near).trans
    (candidateDistancePrefixInto_callerFrame offset refs store other distance)

/-- Original external inputs, next exponent inputs, distance predicate and saved selection. -/
structure DistanceScaleFacts {N m ell : Nat} {kind : ProblemKind}
    {ctx : RuntimeCtx kind} (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (before after : Store ctx) : Prop where
  initial : LatticeCandidateSlotOutcome.InitialConditions input generator samples refs after
  exponentInitial : LatticeCandidateExponent.InitialConditions after refs.exponent m
    (RSA.shortLogPointAtOffset m ell samples offset).2.2
  nearTarget : (after.read (writeInput refs.nearTarget.accepted)).toBool =
    decide (RSA.ShortLogNearTarget m ell samples
      (RSA.shortLogPointAtOffset m ell samples offset))
  selectedFrame : LatticeCandidateSlotMachine.selectedOption refs.selector.selection after =
    LatticeCandidateSlotMachine.selectedOption refs.selector.selection before

/-- Actual distance and range instructions establish the original source checks and next input. -/
lemma distanceScaleStore_correct {N m ell : Nat} {model : ExecutionModel}
    [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (input : Input N) (generator : (ZMod N)ˣ)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3)
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (RSA.ShortLogWidths.coordinateWidth N m ell) (modulusBits N))
    (separation : LatticeCandidateSlotMachine.Separation refs)
    (frameSeparation : FrameSeparation refs) (store : Store ctx)
    (initial : LatticeCandidateSlotOutcome.InitialConditions input generator samples refs store) :
    DistanceScaleFacts input generator samples offset refs store
      (distanceScaleStore (model := model) offset refs store) := by
  let point := RSA.shortLogPointAtOffset m ell samples offset
  let target := RSA.shortLogLatticeTarget m ell samples
  let distance := NumberTheory.integerPointSquaredNorm (point.sub target)
  let afterDistance :=
    (LatticeCandidateDistancePrefix.prefixStep (model := model)
      offset refs.distance store).1
  let afterScale := distanceScaleStore (model := model) offset refs store
  have distanceInitial : LatticeCandidateDistancePrefix.InitialConditions m ell samples
      target refs.distance store := ⟨initial.basis, initial.center, initial.originalTarget⟩
  have distanceFacts := LatticeCandidateDistancePrefix.candidateDistancePrefixInto_correct
    m ell samples offset target refs.distance separation.distance store distanceInitial
  have initialAtDistance :
      LatticeCandidateSlotOutcome.InitialConditions input generator samples refs afterDistance :=
    initialConditions_transport input generator samples refs store afterDistance initial
      fun source =>
      candidateDistancePrefixInto_callerFrame offset refs store (externalSourceInput refs source)
        (frameSeparation.externalAvoidsStage source .distance)
  have initialAtScale :
      LatticeCandidateSlotOutcome.InitialConditions input generator samples refs afterScale :=
    initialConditions_transport input generator samples refs store afterScale initial fun source =>
      distanceScaleStore_callerFrame offset refs store (externalSourceInput refs source)
        (frameSeparation.externalAvoidsStage source .distance)
        (frameSeparation.externalAvoidsStage source .near)
  have distanceAsSquaredDistance :
      distance = NumberTheory.squaredDistance point.toVector target.toVector :=
    NumberTheory.integerPointSquaredNorm_sub point target
  have operandsFit :
      distance < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) ∧
        2 ^ m < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) ∧
          8 * distance < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) ∧
            (2 ^ m) * (2 ^ m) < CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) ∧
              9 * ((2 ^ m) * (2 ^ m)) <
                CShape.wordModulus (RSA.ShortLogWidths.coordinateWidth N m ell) := by
    rw [distanceAsSquaredDistance]
    exact LatticeShortLogCandidatePoint.nearTargetOperandsFit N m ell samples hoffset
  have scaleInitial :
      LatticeNearTargetScale.InitialConditions afterDistance refs.nearTarget distance (2 ^ m) := by
    refine ⟨?_, ?_, operandsFit.1, operandsFit.2.1, operandsFit.2.2.1,
      operandsFit.2.2.2.1, operandsFit.2.2.2.2⟩
    · rw [refs.nearTargetDistance]
      exact distanceFacts.squaredDistance
    · rw [refs.nearTargetUpperBound]
      exact initialAtDistance.upperBound
  have scaleFacts := LatticeNearTargetScale.scaleInto_correct refs.nearTarget separation.nearTarget
    afterDistance distance (2 ^ m) scaleInitial
  have candidateThirdAtScale : RawSignedRepresents
      (afterScale.read (LatticeCandidateExponent.candidateInput refs.exponent)) point.2.2 := by
    change RawSignedRepresents
      (afterScale.read (LatticeState.coordinateInput refs.exponent.point.third)) _
    rw [refs.exponentPoint]
    have pointFrame :
        afterScale.read (LatticeState.coordinateInput refs.distance.candidate.point.third) =
          afterDistance.read (LatticeState.coordinateInput refs.distance.candidate.point.third) :=
      scaleInto_callerFrame refs afterDistance _
        (mutableWrite_avoids_stage refs frameSeparation refs.distance.candidate.point.third
          (.candidate .pointThird) .near rfl (by intro impossible; exact impossible))
    rw [pointFrame]
    exact distanceFacts.point.2.2
  have pointFits := LatticeShortLogCandidatePoint.pointSignedRepresentable N m ell samples hoffset
  have exponentInitial : LatticeCandidateExponent.InitialConditions afterScale refs.exponent m
      point.2.2 := by
    refine ⟨RSA.ShortLogWidths.coordinateWidth_pos N m ell, candidateThirdAtScale, pointFits.2.2,
      ?_, ?_, operandsFit.2.1⟩
    · rw [refs.exponentZero]
      exact initialAtScale.zero
    · rw [refs.exponentUpperBound]
      exact initialAtScale.upperBound
  have nearTarget : (afterScale.read (writeInput refs.nearTarget.accepted)).toBool =
      decide (RSA.ShortLogNearTarget m ell samples point) := by
    refine scaleFacts.accepted.trans ?_
    simp only [distance, target,
      LatticeShortLogCandidatePoint.shortLogNearTarget_iff_scaledSquaredDistance]
  have selectedAcceptedFrame := distanceScaleStore_callerFrame offset refs store
    (writeInput refs.selector.selection.accepted)
    (mutableWrite_avoids_stage refs frameSeparation refs.selector.selection.accepted
      (.selection .accepted) .distance rfl (by intro impossible; exact impossible))
    (mutableWrite_avoids_stage refs frameSeparation refs.selector.selection.accepted
      (.selection .accepted) .near rfl (by intro impossible; exact impossible))
  have selectedValueFrame := distanceScaleStore_callerFrame offset refs store
    (writeInput refs.selector.selection.selected)
    (mutableWrite_avoids_stage refs frameSeparation refs.selector.selection.selected
      (.selection .selected) .distance rfl (by intro impossible; exact impossible))
    (mutableWrite_avoids_stage refs frameSeparation refs.selector.selection.selected
      (.selection .selected) .near rfl (by intro impossible; exact impossible))
  refine ⟨initialAtScale, exponentInitial, nearTarget, ?_⟩
  unfold LatticeCandidateSlotMachine.selectedOption
  rw [selectedAcceptedFrame, selectedValueFrame]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotSemantics
