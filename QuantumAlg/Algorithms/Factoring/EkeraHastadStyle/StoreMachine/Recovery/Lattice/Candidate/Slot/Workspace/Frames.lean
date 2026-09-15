/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Frames

/-!
# Exact physical-to-semantic frame mapping of the reduced candidate-slot layout
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotWorkspaceSeparation

open Execution

noncomputable section

namespace Layout

/-- Abbreviation for the local cell interface. -/
abbrev Cell := LatticeCandidateSlotWorkspaceLayout.Cell

/-- Abbreviation for the local width interface. -/
abbrev Width (N : Nat) := LatticeCandidateSlotWorkspaceViews.Layout.Width N

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticeCandidateSlotWorkspaceViews.Layout.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  LatticeCandidateSlotWorkspaceViews.Layout.cellRef cells cell

end Layout

/-- Physical cell implementing one named mutable cell of the semantic slot. -/
def physicalCell : LatticeCandidateSlotFrames.MutableCell → Layout.Cell
  | .offset .first => .offsetFirst
  | .offset .second => .offsetSecond
  | .offset .third => .offsetThird
  | .candidate .coefficientFirst => .coefficientFirst
  | .candidate .coefficientSecond => .coefficientSecond
  | .candidate .coefficientThird => .coefficientThird
  | .candidate .pointFirst => .pointFirst
  | .candidate .pointSecond => .pointSecond
  | .candidate .pointThird => .pointThird
  | .candidate .product => .pointProduct
  | .difference .first => .differenceFirst
  | .difference .second => .differenceSecond
  | .difference .third => .differenceThird
  | .squaredDistance => .squaredDistance
  | .distanceProduct => .distanceProduct
  | .nearTarget .scaledDistance => .scaledDistance
  | .nearTarget .rangeSquare => .rangeSquare
  | .nearTarget .scaledRange => .scaledRange
  | .nearTarget .accepted => .nearAccepted
  | .exponent .negative => .negative
  | .exponent .magnitude => .magnitude
  | .exponent .exponent => .exponent
  | .exponent .positive => .positive
  | .exponent .belowUpper => .belowUpper
  | .exponent .nonnegative => .nonnegative
  | .exponent .accepted => .exponentAccepted
  | .power => .power
  | .powerAccepted => .powerAccepted
  | .selectorIntermediate => .selectorIntermediate
  | .selectorEligible => .selectorEligible
  | .selection .accepted => .shortAccepted
  | .selection .selected => .shortSelected

/-- Semantic mutable cell implemented by one physical slot cell. -/
def mutableCell : Layout.Cell → LatticeCandidateSlotFrames.MutableCell
  | .offsetFirst => .offset .first
  | .offsetSecond => .offset .second
  | .offsetThird => .offset .third
  | .coefficientFirst => .candidate .coefficientFirst
  | .coefficientSecond => .candidate .coefficientSecond
  | .coefficientThird => .candidate .coefficientThird
  | .pointFirst => .candidate .pointFirst
  | .pointSecond => .candidate .pointSecond
  | .pointThird => .candidate .pointThird
  | .pointProduct => .candidate .product
  | .differenceFirst => .difference .first
  | .differenceSecond => .difference .second
  | .differenceThird => .difference .third
  | .squaredDistance => .squaredDistance
  | .distanceProduct => .distanceProduct
  | .scaledDistance => .nearTarget .scaledDistance
  | .rangeSquare => .nearTarget .rangeSquare
  | .scaledRange => .nearTarget .scaledRange
  | .nearAccepted => .nearTarget .accepted
  | .negative => .exponent .negative
  | .magnitude => .exponent .magnitude
  | .exponent => .exponent .exponent
  | .positive => .exponent .positive
  | .belowUpper => .exponent .belowUpper
  | .nonnegative => .exponent .nonnegative
  | .exponentAccepted => .exponent .accepted
  | .power => .power
  | .powerAccepted => .powerAccepted
  | .selectorIntermediate => .selectorIntermediate
  | .selectorEligible => .selectorEligible
  | .shortAccepted => .selection .accepted
  | .shortSelected => .selection .selected

/-- The physical-to-semantic map is a left inverse of the semantic map. -/
theorem mutableCell_physicalCell (cell : LatticeCandidateSlotFrames.MutableCell) :
    mutableCell (physicalCell cell) = cell := by
  cases cell with
  | offset cell => cases cell <;> rfl
  | candidate cell => cases cell <;> rfl
  | difference cell => cases cell <;> rfl
  | nearTarget cell => cases cell <;> rfl
  | exponent cell => cases cell <;> rfl
  | selection cell => cases cell <;> rfl
  | squaredDistance | distanceProduct | power | powerAccepted |
      selectorIntermediate | selectorEligible => rfl

/-- Named semantic mutable cells map injectively to physical cells. -/
theorem physicalCell_injective : Function.Injective physicalCell :=
  Function.LeftInverse.injective mutableCell_physicalCell

/-- Exact key projection of one semantic cell through the component views. -/
theorem mutableKey_eq_cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (pair : LatticePairNearestPlaneSavedTarget.Refs ctx N)
    (roles : LatticeCandidateSlotWorkspaceViews.NearestOutputRoles pair)
    (constants : LatticeCandidateConstants.Refs ctx (Layout.Width N))
    (setup : LatticeCandidateModularSetup.Refs ctx N)
    (cell : LatticeCandidateSlotFrames.MutableCell) :
    LatticeCandidateSlotFrames.mutableKey
        (LatticeCandidateSlotWorkspaceViews.slotRefs
          cells pair roles constants setup) cell =
      (Layout.cellRef cells (physicalCell cell)).toCStorageRef.key := by
  cases cell with
  | offset cell => cases cell <;> rfl
  | candidate cell => cases cell <;> rfl
  | difference cell => cases cell <;> rfl
  | nearTarget cell => cases cell <;> rfl
  | exponent cell => cases cell <;> rfl
  | selection cell => cases cell <;> rfl
  | squaredDistance | distanceProduct | power | powerAccepted |
      selectorIntermediate | selectorEligible => rfl

/-- Earlier pipeline reads avoid every physical cell of this later allocation. -/
def ExternalAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (refs : LatticeCandidateSlotMachine.Refs ctx
      (Layout.Width N) (modulusBits N)) : Prop :=
  ∀ source cell,
    (Layout.cellRef cells cell).key ∉
      (LatticeCandidateSlotFrames.externalSourceInput refs source).storageKeys

/-- Physical distinctness and earlier-input avoidance supply unified frames. -/
theorem frameSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (pair : LatticePairNearestPlaneSavedTarget.Refs ctx N)
    (roles : LatticeCandidateSlotWorkspaceViews.NearestOutputRoles pair)
    (constants : LatticeCandidateConstants.Refs ctx (Layout.Width N))
    (setup : LatticeCandidateModularSetup.Refs ctx N)
    (externalAvoids : ExternalAvoids cells
      (LatticeCandidateSlotWorkspaceViews.slotRefs
        cells pair roles constants setup)) :
    LatticeCandidateSlotFrames.FrameSeparation
      (LatticeCandidateSlotWorkspaceViews.slotRefs
        cells pair roles constants setup) := by
  let refs := LatticeCandidateSlotWorkspaceViews.slotRefs
    cells pair roles constants setup
  refine ⟨?_, ?_⟩
  · intro left right equal
    apply physicalCell_injective
    apply LatticeCandidateSlotWorkspaceLayout.cellRef_key_injective cells distinct
    simpa only [refs, mutableKey_eq_cellRef] using equal
  · intro source target
    rw [mutableKey_eq_cellRef]
    exact externalAvoids source (physicalCell target)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotWorkspaceSeparation
