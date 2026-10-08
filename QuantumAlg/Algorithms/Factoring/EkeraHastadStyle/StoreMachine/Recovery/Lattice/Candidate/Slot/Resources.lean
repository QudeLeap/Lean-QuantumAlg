/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Program

/-!
# Actual complete candidate-slot native resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotMachine

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {coordinateWidth modulusWidth : Nat}

/-- Independent native allowance for either original signed-magnitude normalization arm. -/
def exponentEnvelope (execution : ExecutionModel) [BitWord.Selected execution]
    (width : Nat) : ResourcePool execution :=
  ResourcePool.max (ResourcePool.ofList (LatticeCandidateExponent.exponentTrace width false))
    (ResourcePool.ofList (LatticeCandidateExponent.exponentTrace width true))

/-- Independent complete five-stage allowance, including literal offset loading and real power
work. -/
def candidateSlotEventEnvelope (execution : ExecutionModel) [BitWord.Selected execution]
    (coordinateWidth modulusWidth : Nat)
    (offset : NumberTheory.IntegerPoint3) : ResourcePool execution :=
  ResourcePool.ofList (LatticeCandidateDistancePrefix.prefixTrace coordinateWidth offset) +
    (ResourcePool.ofList (LatticeNearTargetScale.scaleTrace coordinateWidth) +
      (exponentEnvelope execution coordinateWidth +
        (LatticeCandidatePowerMachine.candidatePowerEventEnvelope execution modulusWidth
          coordinateWidth +
          LatticeCandidateSelector.candidateSelectorEventEnvelope execution coordinateWidth)))

/-- Independent unit-duration bound for initialization, all original checks and native powering. -/
def candidateSlotDepthBound (coordinateWidth modulusWidth : Nat)
    (offset : NumberTheory.IntegerPoint3) : Nat :=
  LatticeOffsetMaterializer.operationCount offset + 2 * modulusWidth + 6 * coordinateWidth + 57

/-- The actual complete trace contains the original fixed prefix and only the chosen later arms. -/
theorem candidateSlotInto_events (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx coordinateWidth modulusWidth)
    (path : (candidateSlotInto spec offset refs).Path) :
    (candidateSlotInto spec offset refs).eventTrace path =
      LatticeCandidateDistancePrefix.prefixTrace coordinateWidth offset ++
        (LatticeNearTargetScale.scaleTrace coordinateWidth ++
          ((LatticeCandidateExponent.candidateExponentInto refs.exponent).eventTrace path.2.2.1 ++
            ((LatticeCandidatePowerMachine.candidatePowerInto spec refs.power).eventTrace
              path.2.2.2.1 ++
              (LatticeCandidateSelector.candidateSelectorInto refs.selector).eventTrace
                path.2.2.2.2))) :=
  congrArg₂ List.append
    (LatticeCandidateDistancePrefix.candidateDistancePrefixInto_events offset refs.distance path.1)
    (congrArg₂ List.append (LatticeNearTargetScale.scaleInto_events refs.nearTarget path.2.1) rfl)

private theorem exponent_pool_le (refs : Refs ctx coordinateWidth modulusWidth)
    (path : (LatticeCandidateExponent.candidateExponentInto refs.exponent).Path) :
    (LatticeCandidateExponent.candidateExponentInto refs.exponent).resourcePool path ≤
      exponentEnvelope model coordinateWidth := by
  refine (LatticeCandidateExponent.candidateExponentInto_resourcePool
    refs.exponent path).le.trans ?_
  cases path.1.2.1.toBool
  · exact ResourcePool.le_max_left _ _
  · exact ResourcePool.le_max_right _ _

/-- Actual native multiplicities satisfy the independent allowance of all five original stages. -/
theorem candidateSlotInto_pool_le (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx coordinateWidth modulusWidth)
    (path : (candidateSlotInto spec offset refs).Path) :
    (candidateSlotInto spec offset refs).resourcePool path ≤
      candidateSlotEventEnvelope model coordinateWidth modulusWidth offset := by
  change ResourcePool.ofList (_ ++ (_ ++ (_ ++ (_ ++ _)))) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add
    (LatticeCandidateDistancePrefix.candidateDistancePrefixInto_resourcePool
      offset refs.distance path.1).le
    (add_le_add (LatticeNearTargetScale.scaleInto_resourcePool refs.nearTarget path.2.1).le
      (add_le_add (exponent_pool_le refs path.2.2.1)
        (add_le_add (LatticeCandidatePowerMachine.candidatePowerInto_pool_le
          spec refs.power path.2.2.2.1)
          (LatticeCandidateSelector.candidateSelectorInto_pool_le refs.selector path.2.2.2.2))))

/-- Actual depth includes every initialization, arithmetic check and selected-copy dependency. -/
theorem candidateSlotInto_depth_le (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx coordinateWidth modulusWidth)
    (path : (candidateSlotInto spec offset refs).Path) :
    (candidateSlotInto spec offset refs).depth (fun _ => 1) path ≤
      candidateSlotDepthBound coordinateWidth modulusWidth offset := by
  have combined := Nat.add_le_add
    (LatticeCandidateDistancePrefix.candidateDistancePrefixInto_depth
      offset refs.distance path.1).le
    (Nat.add_le_add (LatticeNearTargetScale.scaleInto_depth refs.nearTarget path.2.1).le
      (Nat.add_le_add (LatticeCandidateExponent.candidateExponentInto_depth_le
        refs.exponent path.2.2.1)
        (Nat.add_le_add (LatticeCandidatePowerMachine.candidatePowerInto_unitDepth_le
          spec refs.power path.2.2.2.1)
          (LatticeCandidateSelector.candidateSelectorInto_depth_le refs.selector path.2.2.2.2))))
  refine combined.trans ?_
  unfold candidateSlotDepthBound LatticeCandidateDistancePrefix.operationCount
  omega

/-- The entire actual candidate slot restores every borrowed system with arbitrary references. -/
theorem candidateSlotInto_borrowedRestored (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx coordinateWidth modulusWidth)
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidateSlotInto spec offset refs).BorrowedRestored Reference state
      ((candidateSlotInto spec offset refs).execute Reference state) := by
  refine Circuit.borrowedRestored_seq
    (LatticeCandidateDistancePrefix.candidateDistancePrefixInto offset refs.distance) _ state
    (LatticeCandidateDistancePrefix.candidateDistancePrefixInto_borrowedRestored
      offset refs.distance Reference state) ?_
  refine Circuit.borrowedRestored_seq (LatticeNearTargetScale.scaleInto refs.nearTarget) _ _
    (LatticeNearTargetScale.scaleInto_borrowedRestored refs.nearTarget Reference _) ?_
  refine Circuit.borrowedRestored_seq
    (LatticeCandidateExponent.candidateExponentInto refs.exponent) _ _
    (LatticeCandidateExponent.candidateExponentInto_borrowedRestored refs.exponent Reference _) ?_
  exact Circuit.borrowedRestored_seq _ _ _
    (LatticeCandidatePowerMachine.candidatePowerInto_borrowedRestored spec refs.power Reference _)
    (LatticeCandidateSelector.candidateSelectorInto_borrowedRestored refs.selector Reference _)

/-- Actual resident peak counts every original cell and all simultaneous native-power scratch. -/
theorem candidateSlotInto_resident_le (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx coordinateWidth modulusWidth)
    (path : (candidateSlotInto spec offset refs).Path) :
    (candidateSlotInto spec offset refs).peakResidentSpace path ≤ ctx.residentSpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind modulusWidth := by
  refine (Circuit.peakResidentSpace_seq
    (LatticeCandidateDistancePrefix.candidateDistancePrefixInto offset refs.distance)
    (rangeChecksInto spec refs) path).le.trans ?_
  apply SpacePool.max_le
  · exact (LatticeCandidateDistancePrefix.candidateDistancePrefixInto_resident_le
      offset refs.distance path.1).trans (le_add_of_nonneg_right zero_le)
  · refine (Circuit.peakResidentSpace_seq (LatticeNearTargetScale.scaleInto refs.nearTarget)
      (exponentChecksInto spec refs) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (LatticeNearTargetScale.scaleInto_resident_le refs.nearTarget path.2.1).trans
        (le_add_of_nonneg_right zero_le)
    · refine (Circuit.peakResidentSpace_seq
        (LatticeCandidateExponent.candidateExponentInto refs.exponent)
        (powerSelectionInto spec refs) path.2.2).le.trans ?_
      apply SpacePool.max_le
      · exact (LatticeCandidateExponent.candidateExponentInto_resident_le
          refs.exponent path.2.2.1).trans (le_add_of_nonneg_right zero_le)
      · refine (Circuit.peakResidentSpace_seq
          (LatticeCandidatePowerMachine.candidatePowerInto spec refs.power)
          (LatticeCandidateSelector.candidateSelectorInto refs.selector) path.2.2.2).le.trans ?_
        apply SpacePool.max_le
        · exact LatticeCandidatePowerMachine.candidatePowerInto_resident_le
            spec refs.power path.2.2.2.1
        · exact (LatticeCandidateSelector.candidateSelectorInto_resident_le
            refs.selector path.2.2.2.2).trans (le_add_of_nonneg_right zero_le)

/-- Actual auxiliary peak counts every original cell and all simultaneous native-power scratch. -/
theorem candidateSlotInto_auxiliary_le (spec : ModulusSpec modulusWidth)
    (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx coordinateWidth modulusWidth)
    (path : (candidateSlotInto spec offset refs).Path) :
    (candidateSlotInto spec offset refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind modulusWidth := by
  refine (Circuit.peakAuxiliarySpace_seq
    (LatticeCandidateDistancePrefix.candidateDistancePrefixInto offset refs.distance)
    (rangeChecksInto spec refs) path).le.trans ?_
  apply SpacePool.max_le
  · exact (LatticeCandidateDistancePrefix.candidateDistancePrefixInto_auxiliary_le
      offset refs.distance path.1).trans (le_add_of_nonneg_right zero_le)
  · refine (Circuit.peakAuxiliarySpace_seq (LatticeNearTargetScale.scaleInto refs.nearTarget)
      (exponentChecksInto spec refs) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (LatticeNearTargetScale.scaleInto_auxiliary_le refs.nearTarget path.2.1).trans
        (le_add_of_nonneg_right zero_le)
    · refine (Circuit.peakAuxiliarySpace_seq
        (LatticeCandidateExponent.candidateExponentInto refs.exponent)
        (powerSelectionInto spec refs) path.2.2).le.trans ?_
      apply SpacePool.max_le
      · exact (LatticeCandidateExponent.candidateExponentInto_auxiliary_le
          refs.exponent path.2.2.1).trans (le_add_of_nonneg_right zero_le)
      · refine (Circuit.peakAuxiliarySpace_seq
          (LatticeCandidatePowerMachine.candidatePowerInto spec refs.power)
          (LatticeCandidateSelector.candidateSelectorInto refs.selector) path.2.2.2).le.trans ?_
        apply SpacePool.max_le
        · exact LatticeCandidatePowerMachine.candidatePowerInto_auxiliary_le
            spec refs.power path.2.2.2.1
        · exact (LatticeCandidateSelector.candidateSelectorInto_auxiliary_le
            refs.selector path.2.2.2.2).trans (le_add_of_nonneg_right zero_le)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotMachine
