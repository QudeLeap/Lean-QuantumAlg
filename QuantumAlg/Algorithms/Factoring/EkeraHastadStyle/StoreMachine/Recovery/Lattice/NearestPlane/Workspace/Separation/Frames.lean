/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Separation.Keys

/-!
# Nearest-plane physical caller frames
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical
namespace LatticeNearestPlaneScratchWorkspaceSeparation

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

private theorem coordinateInputAvoidsPhysical {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {targetShape : CShape}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch)
    (source : CWriteRef ctx (LatticeState.RawSignedWordShape
      (LatticePairStateWorkspaceLayout.Width N)))
    (target : CWriteRef ctx targetShape)
    (sourceCell targetCell : PhysicalCell)
    (sourceKey : source.toCStorageRef.key =
      physicalKey state scratch sourceCell)
    (targetKey : target.toCStorageRef.key =
      physicalKey state scratch targetCell)
    (different : sourceCell ≠ targetCell) :
    target.toCStorageRef.key ∉ (LatticeState.coordinateInput source).storageKeys := by
  apply storageRead_not_mem
  rw [sourceKey, targetKey]
  intro equal
  exact different (physicalKey_injective certificates equal)

private theorem writeInputAvoidsPhysical {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {sourceShape targetShape : CShape}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch)
    (source : CWriteRef ctx sourceShape) (target : CWriteRef ctx targetShape)
    (sourceCell targetCell : PhysicalCell)
    (sourceKey : source.toCStorageRef.key =
      physicalKey state scratch sourceCell)
    (targetKey : target.toCStorageRef.key =
      physicalKey state scratch targetCell)
    (different : sourceCell ≠ targetCell) :
    target.toCStorageRef.key ∉ (SignedWord.writeInput source).storageKeys := by
  apply storageRead_not_mem
  rw [sourceKey, targetKey]
  intro equal
  exact different (physicalKey_injective certificates equal)

private inductive ThirdWriteCell where
  | productLeft | productRight
  | crossFirst | crossSecond | crossThird
  | dotProduct | numerator | denominator | denominatorMagnitude
  | divisionMagnitude | divisionNegative
  | divisionWideNumerator | divisionWideDenominator
  | divisionQuotientRemainder | divisionOutput | reduceProduct
  | targetFirst | targetSecond | targetThird
deriving DecidableEq

private def thirdWritePhysicalCell : ThirdWriteCell → PhysicalCell
  | .productLeft => .inr .crossProductLeft
  | .productRight => .inr .crossProductRight
  | .crossFirst => .inr .crossFirst
  | .crossSecond => .inr .crossSecond
  | .crossThird => .inr .crossThird
  | .dotProduct => .inr .dotProduct
  | .numerator => .inr .numerator
  | .denominator => .inr .denominator
  | .denominatorMagnitude => .inr .g11
  | .divisionMagnitude => .inr .divisionMagnitude
  | .divisionNegative => .inr .divisionNegative
  | .divisionWideNumerator => .inr .divisionWideNumerator
  | .divisionWideDenominator => .inr .divisionWideDenominator
  | .divisionQuotientRemainder => .inr .divisionQuotientRemainder
  | .divisionOutput => .inr .thirdOutput
  | .reduceProduct => .inr .reduceProduct
  | .targetFirst => .inl .targetFirst
  | .targetSecond => .inl .targetSecond
  | .targetThird => .inl .targetThird

private theorem thirdFrameAvoidsOf {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N)
    (other : CInputRef ctx shape)
    (avoids : ∀ target,
      physicalKey state scratch (thirdWritePhysicalCell target) ∉ other.storageKeys) :
    LatticeNearestPlaneThree.ThirdFrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state scratch) other := by
  intro cell member
  simp only [LatticeNearestPlaneThird.mutableCells, LatticeNearestPlaneThird.prefixCells,
    LatticeNearestPlaneThird.suffixCells, LatticeNearestPlaneThird.beforeReductionCells,
    LatticeNearestPlaneThird.divisionCells, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact avoids .crossFirst
  · exact avoids .crossSecond
  · exact avoids .crossThird
  · exact avoids .productLeft
  · exact avoids .productRight
  · exact avoids .dotProduct
  · exact avoids .numerator
  · exact avoids .denominator
  · exact avoids .denominatorMagnitude
  · exact avoids .numerator
  · exact avoids .divisionMagnitude
  · exact avoids .divisionNegative
  · exact avoids .divisionWideNumerator
  · exact avoids .divisionWideDenominator
  · exact avoids .divisionQuotientRemainder
  · exact avoids .divisionOutput
  · exact avoids .reduceProduct
  · exact avoids .targetFirst
  · exact avoids .targetSecond
  · exact avoids .targetThird

private theorem thirdFrameAvoidsCoordinate {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch)
    (source : CWriteRef ctx (LatticeState.RawSignedWordShape
      (LatticePairStateWorkspaceLayout.Width N)))
    (sourceCell : PhysicalCell)
    (sourceKey : source.toCStorageRef.key =
      physicalKey state scratch sourceCell)
    (different : ∀ target, sourceCell ≠ thirdWritePhysicalCell target) :
    LatticeNearestPlaneThree.ThirdFrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
      (LatticeState.coordinateInput source) := by
  apply thirdFrameAvoidsOf state scratch
  intro target
  apply storageRead_not_mem
  rw [sourceKey]
  intro equal
  exact different target (physicalKey_injective certificates equal)

private theorem coordinateInputAvoidsPhysicalKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch)
    (source : CWriteRef ctx (LatticeState.RawSignedWordShape
      (LatticePairStateWorkspaceLayout.Width N)))
    (sourceCell targetCell : PhysicalCell)
    (sourceKey : source.toCStorageRef.key =
      physicalKey state scratch sourceCell)
    (different : sourceCell ≠ targetCell) :
    physicalKey state scratch targetCell ∉ (LatticeState.coordinateInput source).storageKeys := by
  apply storageRead_not_mem
  rw [sourceKey]
  intro equal
  exact different (physicalKey_injective certificates equal)

private theorem writeInputAvoidsPhysicalKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch)
    (source : CWriteRef ctx shape) (sourceCell targetCell : PhysicalCell)
    (sourceKey : source.toCStorageRef.key =
      physicalKey state scratch sourceCell)
    (different : sourceCell ≠ targetCell) :
    physicalKey state scratch targetCell ∉ (SignedWord.writeInput source).storageKeys := by
  apply storageRead_not_mem
  rw [sourceKey]
  intro equal
  exact different (physicalKey_injective certificates equal)

private inductive SecondWriteCell where
  | crossProductLeft | crossProductRight
  | crossFirst | crossSecond | crossThird
  | dotProduct | g11 | g21 | targetDotSecond | targetDotFirst
  | denominator | numerator | numeratorProduct
  | divisionMagnitude | divisionNegative
  | divisionWideNumerator | divisionWideDenominator
  | divisionQuotientRemainder | divisionOutput | reduceProduct
  | targetFirst | targetSecond | targetThird
deriving DecidableEq

private def secondWritePhysicalCell : SecondWriteCell → PhysicalCell
  | .crossProductLeft => .inr .crossProductLeft
  | .crossProductRight => .inr .crossProductRight
  | .crossFirst => .inr .crossFirst
  | .crossSecond => .inr .crossSecond
  | .crossThird => .inr .crossThird
  | .dotProduct => .inr .dotProduct
  | .g11 => .inr .g11
  | .g21 => .inr .g21
  | .targetDotSecond => .inr .targetDotSecond
  | .targetDotFirst => .inr .targetDotFirst
  | .denominator => .inr .denominator
  | .numerator => .inr .numerator
  | .numeratorProduct => .inr .numeratorProduct
  | .divisionMagnitude => .inr .divisionMagnitude
  | .divisionNegative => .inr .divisionNegative
  | .divisionWideNumerator => .inr .divisionWideNumerator
  | .divisionWideDenominator => .inr .divisionWideDenominator
  | .divisionQuotientRemainder => .inr .divisionQuotientRemainder
  | .divisionOutput => .inr .secondOutput
  | .reduceProduct => .inr .reduceProduct
  | .targetFirst => .inl .targetFirst
  | .targetSecond => .inl .targetSecond
  | .targetThird => .inl .targetThird

private theorem secondFrameAvoidsOf {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N)
    (other : CInputRef ctx shape)
    (avoids : ∀ target,
      physicalKey state scratch (secondWritePhysicalCell target) ∉ other.storageKeys) :
    LatticeNearestPlaneThree.SecondFrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state scratch)
      other := by
  intro key member
  simp only [LatticeNearestPlaneSecond.mutableKeys, LatticeNearestPlaneSecond.prefixKeys,
    SignedWord.RoundedDiv.mutableKeys, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact avoids .crossFirst
  · exact avoids .crossSecond
  · exact avoids .crossThird
  · exact avoids .crossProductLeft
  · exact avoids .crossProductRight
  · exact avoids .dotProduct
  · exact avoids .g11
  · exact avoids .g21
  · exact avoids .targetDotSecond
  · exact avoids .targetDotFirst
  · exact avoids .denominator
  · exact avoids .numerator
  · exact avoids .numeratorProduct
  · exact avoids .divisionMagnitude
  · exact avoids .divisionNegative
  · exact avoids .divisionWideNumerator
  · exact avoids .divisionWideDenominator
  · exact avoids .divisionQuotientRemainder
  · exact avoids .divisionOutput
  · exact avoids .reduceProduct
  · exact avoids .targetFirst
  · exact avoids .targetSecond
  · exact avoids .targetThird

private theorem secondFrameAvoidsCoordinate {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch)
    (source : CWriteRef ctx (LatticeState.RawSignedWordShape
      (LatticePairStateWorkspaceLayout.Width N)))
    (sourceCell : PhysicalCell)
    (sourceKey : source.toCStorageRef.key =
      physicalKey state scratch sourceCell)
    (different : ∀ target, sourceCell ≠ secondWritePhysicalCell target) :
    LatticeNearestPlaneThree.SecondFrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
      (LatticeState.coordinateInput source) := by
  apply secondFrameAvoidsOf state scratch
  intro target
  exact coordinateInputAvoidsPhysicalKey certificates source sourceCell
    (secondWritePhysicalCell target) sourceKey (different target)

private theorem secondFrameAvoidsWrite {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch)
    (source : CWriteRef ctx shape) (sourceCell : PhysicalCell)
    (sourceKey : source.toCStorageRef.key =
      physicalKey state scratch sourceCell)
    (different : ∀ target, sourceCell ≠ secondWritePhysicalCell target) :
    LatticeNearestPlaneThree.SecondFrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
      (SignedWord.writeInput source) := by
  apply secondFrameAvoidsOf state scratch
  intro target
  exact writeInputAvoidsPhysicalKey certificates source sourceCell
    (secondWritePhysicalCell target) sourceKey (different target)

private inductive FirstWriteCell where
  | dotProduct | numerator | normProduct | denominator
  | divisionMagnitude | divisionNegative
  | divisionWideNumerator | divisionWideDenominator
  | divisionQuotientRemainder | divisionOutput | reduceProduct
  | targetFirst | targetSecond | targetThird
deriving DecidableEq

private def firstWritePhysicalCell : FirstWriteCell → PhysicalCell
  | .dotProduct => .inr .dotProduct
  | .numerator => .inr .numerator
  | .normProduct => .inr .numeratorProduct
  | .denominator => .inr .denominator
  | .divisionMagnitude => .inr .divisionMagnitude
  | .divisionNegative => .inr .divisionNegative
  | .divisionWideNumerator => .inr .divisionWideNumerator
  | .divisionWideDenominator => .inr .divisionWideDenominator
  | .divisionQuotientRemainder => .inr .divisionQuotientRemainder
  | .divisionOutput => .inr .targetDotSecond
  | .reduceProduct => .inr .reduceProduct
  | .targetFirst => .inl .targetFirst
  | .targetSecond => .inl .targetSecond
  | .targetThird => .inl .targetThird

private theorem firstFrameAvoidsOf {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N)
    (other : CInputRef ctx shape)
    (avoids : ∀ target,
      physicalKey state scratch (firstWritePhysicalCell target) ∉ other.storageKeys) :
    LatticeNearestPlaneThree.FirstFrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state scratch)
      other := by
  let refs := LatticeNearestPlaneScratchWorkspaceViews.nearestRefs state scratch
  change LatticeNearestPlaneThree.FirstFrameAvoids refs other
  refine {
    dotProduct := avoids .dotProduct
    numerator := avoids .numerator
    normProduct := avoids .normProduct
    denominator := avoids .denominator
    division := ?_
    reduceProduct := avoids .reduceProduct
    targetFirst := avoids .targetFirst
    targetSecond := avoids .targetSecond
    targetThird := avoids .targetThird }
  intro key member
  simp only [SignedWord.RoundedDiv.mutableKeys, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact avoids .divisionMagnitude
  · exact avoids .divisionNegative
  · exact avoids .divisionWideNumerator
  · exact avoids .divisionWideDenominator
  · exact avoids .divisionQuotientRemainder
  · exact avoids .divisionOutput

private theorem firstFrameAvoidsWrite {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch)
    (source : CWriteRef ctx shape) (sourceCell : PhysicalCell)
    (sourceKey : source.toCStorageRef.key =
      physicalKey state scratch sourceCell)
    (different : ∀ target, sourceCell ≠ firstWritePhysicalCell target) :
    LatticeNearestPlaneThree.FirstFrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
      (SignedWord.writeInput source) := by
  apply firstFrameAvoidsOf state scratch
  intro target
  exact writeInputAvoidsPhysicalKey certificates source sourceCell
    (firstWritePhysicalCell target) sourceKey (different target)

/-- Any persistent state coordinate other than the three mutable target
coordinates is framed by the complete nearest-plane routine. -/
theorem frameAvoidsStateCoordinate {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch)
    (source : CWriteRef ctx (LatticeState.RawSignedWordShape
      (LatticePairStateWorkspaceLayout.Width N)))
    (sourceCell : LatticePairStateWorkspaceLayout.Cell)
    (sourceKey : source.toCStorageRef.key =
      physicalKey state scratch (.inl sourceCell))
    (avoidsFirst : sourceCell ≠ .targetFirst)
    (avoidsSecond : sourceCell ≠ .targetSecond)
    (avoidsThird : sourceCell ≠ .targetThird) :
    LatticeNearestPlaneThree.FrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch)
      (LatticeState.coordinateInput source) := by
  refine ⟨thirdFrameAvoidsCoordinate certificates source (.inl sourceCell)
      sourceKey ?_,
    secondFrameAvoidsCoordinate certificates source (.inl sourceCell)
      sourceKey ?_, ?_⟩
  · intro target
    cases target <;>
      simp [thirdWritePhysicalCell, avoidsFirst, avoidsSecond, avoidsThird]
  · intro target
    cases target <;>
      simp [secondWritePhysicalCell, avoidsFirst, avoidsSecond, avoidsThird]
  · exact firstFrameAvoidsWrite certificates source (.inl sourceCell)
      sourceKey (by
        intro target
        cases target <;>
          simp [firstWritePhysicalCell, avoidsFirst, avoidsSecond, avoidsThird])

/-- Avoiding every persistent state and nearest scratch cell is sufficient for
the complete nearest-plane caller-frame contract. -/
theorem frameAvoids_of_physical {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (_certificates : PhysicalSeparation state scratch)
    (other : CInputRef ctx shape)
    (avoidsState : ∀ cell,
      (LatticePairStateWorkspaceLayout.cellRef state cell).key ∉ other.storageKeys)
    (avoidsScratch : ∀ cell,
      (LatticeNearestPlaneScratchWorkspaceLayout.cellRef scratch cell).key ∉ other.storageKeys) :
    LatticeNearestPlaneThree.FrameAvoids
      (LatticeNearestPlaneScratchWorkspaceViews.nearestRefs
        state scratch) other := by
  have avoidsPhysical (cell : PhysicalCell) :
      physicalKey state scratch cell ∉ other.storageKeys := by
    rcases cell with cell | cell
    · exact avoidsState cell
    · exact avoidsScratch cell
  exact ⟨thirdFrameAvoidsOf state scratch other
      (fun target => avoidsPhysical (thirdWritePhysicalCell target)),
    secondFrameAvoidsOf state scratch other
      (fun target => avoidsPhysical (secondWritePhysicalCell target)),
    firstFrameAvoidsOf state scratch other
      (fun target => avoidsPhysical (firstWritePhysicalCell target))⟩

end

end LatticeNearestPlaneScratchWorkspaceSeparation
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
