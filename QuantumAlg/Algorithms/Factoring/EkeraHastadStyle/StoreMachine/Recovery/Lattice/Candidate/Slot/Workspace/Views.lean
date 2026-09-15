/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Constants
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget.Layout

/-!
# Actual candidate component views on the reduced physical slot layout
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeCandidateSlotWorkspaceViews

open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

namespace Layout

/-- Abbreviation for the local width interface. -/
abbrev Width (N : Nat) : Nat := LatticeCandidateSlotWorkspaceLayout.Width N

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticeCandidateSlotWorkspaceLayout.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : LatticeCandidateSlotWorkspaceLayout.Cell) :=
  LatticeCandidateSlotWorkspaceLayout.cellRef cells cell

end Layout

/-- Short name for the pair-owned nearest-plane state reused by the slot. -/
abbrev pairNearestRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (pair : LatticePairNearestPlaneSavedTarget.Refs ctx N) :=
  LatticePairNearestPlaneSavedTarget.nearestRefs pair

/-- Workspace proof for the three nearest-plane quotient outputs reused as the
candidate coefficient center. -/
structure NearestOutputRoles {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (pair : LatticePairNearestPlaneSavedTarget.Refs ctx N) : Prop where
  first : (pairNearestRefs pair).first.division.output.toCStorageRef.role = .workspace
  second : (pairNearestRefs pair).second.division.output.toCStorageRef.role = .workspace
  third : (pairNearestRefs pair).third.division.output.toCStorageRef.role = .workspace

/-- Three cells receiving the literal coefficient offset. -/
def offsetRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeState.PointRefs ctx (Layout.Width N) where
  first := Layout.cellRef cells .offsetFirst
  firstRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .offsetFirst
  second := Layout.cellRef cells .offsetSecond
  secondRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .offsetSecond
  third := Layout.cellRef cells .offsetThird
  thirdRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .offsetThird

/-- Three cells receiving the nearest coefficient plus its current offset. -/
def coefficientRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeState.PointRefs ctx (Layout.Width N) where
  first := Layout.cellRef cells .coefficientFirst
  firstRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .coefficientFirst
  second := Layout.cellRef cells .coefficientSecond
  secondRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .coefficientSecond
  third := Layout.cellRef cells .coefficientThird
  thirdRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .coefficientThird

/-- Three cells receiving the materialized lattice candidate point. -/
def pointRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeState.PointRefs ctx (Layout.Width N) where
  first := Layout.cellRef cells .pointFirst
  firstRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .pointFirst
  second := Layout.cellRef cells .pointSecond
  secondRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .pointSecond
  third := Layout.cellRef cells .pointThird
  thirdRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .pointThird

/-- Three cells receiving the candidate-minus-target difference. -/
def differenceRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeState.PointRefs ctx (Layout.Width N) where
  first := Layout.cellRef cells .differenceFirst
  firstRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .differenceFirst
  second := Layout.cellRef cells .differenceSecond
  secondRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .differenceSecond
  third := Layout.cellRef cells .differenceThird
  thirdRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .differenceThird

/-- Persistent first-success latches local to the reusable offset scan. -/
def selectionRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    FirstAccepted.Direct.Refs ctx (Layout.Width N) where
  accepted := Layout.cellRef cells .shortAccepted
  selected := Layout.cellRef cells .shortSelected

/-- Literal candidate-point and squared-distance prefix. -/
def distanceRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (pair : LatticePairNearestPlaneSavedTarget.Refs ctx N)
    (roles : NearestOutputRoles pair) :
    LatticeCandidateDistancePrefix.Refs ctx (Layout.Width N) where
  materializer := { offset := offsetRefs cells }
  candidate :=
    { nearest := LatticePairNearestPlaneSavedTarget.nearestRefs pair
      offset := offsetRefs cells
      coefficient := coefficientRefs cells
      point := pointRefs cells
      product := Layout.cellRef cells .pointProduct
      productRole :=
        LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .pointProduct
      firstOutputRole := roles.first
      secondOutputRole := roles.second
      thirdOutputRole := roles.third }
  distance :=
    { difference :=
        { point := pointRefs cells
          target := pair.savedTarget
          difference := differenceRefs cells }
      squaredDistance := Layout.cellRef cells .squaredDistance
      squaredDistanceRole :=
        LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .squaredDistance
      product := Layout.cellRef cells .distanceProduct
      productRole :=
        LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .distanceProduct }
  originalTarget := pair.savedTarget
  materializerOffset := rfl
  distancePoint := rfl
  distanceTarget := rfl

/-- Distance-threshold scaling and comparison cells. -/
def nearTargetRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (constants : LatticeCandidateConstants.Refs ctx (Layout.Width N)) :
    LatticeNearTargetScale.Refs ctx (Layout.Width N) where
  distance := ClassicalRoutines.NumberTheory.SignedWord.writeInput
    (Layout.cellRef cells .squaredDistance)
  upperBound := LatticeLoading.writeInput constants.upperBound
  scaledDistance := Layout.cellRef cells .scaledDistance
  scaledDistanceRole :=
    LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .scaledDistance
  rangeSquare := Layout.cellRef cells .rangeSquare
  rangeSquareRole :=
    LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .rangeSquare
  scaledRange := Layout.cellRef cells .scaledRange
  scaledRangeRole :=
    LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .scaledRange
  accepted := Layout.cellRef cells .nearAccepted
  acceptedRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .nearAccepted

/-- Candidate-third-coordinate exponent classification cells. -/
def exponentRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (constants : LatticeCandidateConstants.Refs ctx (Layout.Width N)) :
    LatticeCandidateExponent.Refs ctx (Layout.Width N) where
  point := pointRefs cells
  zero := LatticeLoading.writeInput constants.zero
  upperBound := LatticeLoading.writeInput constants.upperBound
  negative := Layout.cellRef cells .negative
  negativeRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .negative
  magnitude := Layout.cellRef cells .magnitude
  magnitudeRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .magnitude
  exponent := Layout.cellRef cells .exponent
  exponentRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .exponent
  positive := Layout.cellRef cells .positive
  positiveRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .positive
  belowUpper := Layout.cellRef cells .belowUpper
  belowUpperRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .belowUpper
  nonnegative := Layout.cellRef cells .nonnegative
  nonnegativeRole :=
    LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .nonnegative
  accepted := Layout.cellRef cells .exponentAccepted
  acceptedRole :=
    LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .exponentAccepted

/-- Modular-power validation cells. -/
def powerRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (setup : LatticeCandidateModularSetup.Refs ctx N) :
    LatticeCandidatePowerMachine.Refs ctx (modulusBits N) (Layout.Width N) where
  modulus := LatticeCandidateModularSetup.writeInput setup.modulus
  generator := LatticeCandidateModularSetup.writeInput setup.generator
  exponent := ClassicalRoutines.NumberTheory.SignedWord.writeInput
    (Layout.cellRef cells .exponent)
  targetPower := LatticeCandidateModularSetup.writeInput setup.targetPower
  power := Layout.cellRef cells .power
  powerRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .power
  accepted := Layout.cellRef cells .powerAccepted
  acceptedRole := LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .powerAccepted

/-- Closing Boolean conjunctions and persistent first-success selector. -/
def selectorRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    LatticeCandidateSelector.Refs ctx (Layout.Width N) where
  nearTarget :=
    LatticeCandidateSelector.writeInput (Layout.cellRef cells .nearAccepted)
  exponentInRange :=
    LatticeCandidateSelector.writeInput (Layout.cellRef cells .exponentAccepted)
  powerMatches :=
    LatticeCandidatePowerMachine.writeInput (Layout.cellRef cells .powerAccepted)
  candidate := ClassicalRoutines.NumberTheory.SignedWord.writeInput
    (Layout.cellRef cells .exponent)
  intermediate := Layout.cellRef cells .selectorIntermediate
  intermediateRole :=
    LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .selectorIntermediate
  eligible := Layout.cellRef cells .selectorEligible
  eligibleRole :=
    LatticeCandidateSlotWorkspaceLayout.cellRef_role cells .selectorEligible
  selection := selectionRefs cells

/-- All five actual component views over one physical slot allocation. -/
def slotRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (pair : LatticePairNearestPlaneSavedTarget.Refs ctx N)
    (roles : NearestOutputRoles pair)
    (constants : LatticeCandidateConstants.Refs ctx (Layout.Width N))
    (setup : LatticeCandidateModularSetup.Refs ctx N) :
    LatticeCandidateSlotMachine.Refs ctx (Layout.Width N) (modulusBits N) where
  distance := distanceRefs cells pair roles
  nearTarget := nearTargetRefs cells constants
  exponent := exponentRefs cells constants
  power := powerRefs cells setup
  selector := selectorRefs cells
  zero := LatticeLoading.writeInput constants.zero
  upperBound := LatticeLoading.writeInput constants.upperBound
  nearTargetDistance := rfl
  nearTargetUpperBound := rfl
  exponentPoint := rfl
  exponentZero := rfl
  exponentUpperBound := rfl
  powerExponent := rfl
  selectorNearTarget := rfl
  selectorExponentInRange := rfl
  selectorPowerMatches := rfl
  selectorCandidate := rfl

end

end LatticeCandidateSlotWorkspaceViews
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
