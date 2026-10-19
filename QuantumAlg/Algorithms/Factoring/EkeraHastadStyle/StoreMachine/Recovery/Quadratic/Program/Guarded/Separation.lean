/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Program.Guarded
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Program.Separation

/-!
# Physical separation for guarded quadratic recovery

The guarded wrapper clears four reusable square-root words before consulting
the preceding short-log selector.  This module derives its complete separation
from physical distinctness and two compact cross-allocation contracts.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace QuadraticGuardSeparation

open Execution
open ClassicalRoutines

noncomputable section

namespace Layout

/-- Abbreviation for the local cell interface. -/
abbrev Cell := QuadraticScratchLayout.Cell

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  QuadraticScratchLayout.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  QuadraticScratchLayout.cellRef cells cell

end Layout

/-- Both visible cells of the preceding selector avoid the quadratic package. -/
structure ShortSelectionSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (selection : FirstAccepted.Direct.Refs ctx
      (QuadraticScratchLayout.ShortWidth N)) : Prop where
  acceptedAvoidsQuadratic : ∀ cell,
    (Layout.cellRef cells cell).toCStorageRef.key ∉
      (FirstAccepted.cellRead selection.accepted).storageKeys
  selectedAvoidsQuadratic : ∀ cell,
    (Layout.cellRef cells cell).toCStorageRef.key ∉
      (FirstAccepted.cellRead selection.selected).storageKeys

/-- Distinct named quadratic cells avoid each other's storage key. -/
private lemma cellAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (left right : Layout.Cell) (different : left ≠ right) :
    (Layout.cellRef cells right).toCStorageRef.key ∉
      (FirstAccepted.cellRead (Layout.cellRef cells left)).storageKeys := by
  intro present
  have equal := List.mem_singleton.mp present
  exact different
    (QuadraticScratchLayout.cellRef_key_injective cells distinct equal.symm)

/-- Physical distinctness supplies the four-word reset separation. -/
private lemma resetSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (factorSelection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N)) :
    QuadraticRecoveryReset.Separation
      (QuadraticScratchViews.resetRefs cells shortLog factorSelection) :=
  ⟨cellAvoids cells distinct .sqrtWideInput .sqrtRoot (by decide),
    cellAvoids cells distinct .sqrtWideInput .sqrtHalf (by decide),
    cellAvoids cells distinct .sqrtWideInput .sqrtOutput (by decide),
    cellAvoids cells distinct .sqrtRoot .sqrtHalf (by decide),
    cellAvoids cells distinct .sqrtRoot .sqrtOutput (by decide),
    cellAvoids cells distinct .sqrtHalf .sqrtOutput (by decide)⟩

/-- Four pointwise avoidances project to the reset caller-frame contract. -/
private lemma resetCallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (factorSelection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N))
    {shape : CShape} (other : CInputRef ctx shape)
    (wide : ((Layout.cellRef cells .sqrtWideInput).toCStorageRef.key ∉ other.storageKeys))
    (root : ((Layout.cellRef cells .sqrtRoot).toCStorageRef.key ∉ other.storageKeys))
    (half : ((Layout.cellRef cells .sqrtHalf).toCStorageRef.key ∉ other.storageKeys))
    (output : ((Layout.cellRef cells .sqrtOutput).toCStorageRef.key ∉ other.storageKeys)) :
    QuadraticRecoveryReset.CallerFrameAvoids
      (QuadraticScratchViews.resetRefs cells shortLog factorSelection) other :=
  ⟨wide, root, half, output⟩

/-- One persistent quadratic constant is framed by the reset. -/
private lemma constantResetFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (factorSelection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N))
    (source : Layout.Cell)
    (allowed : source = .one ∨ source = .zero ∨ source = .modulus) :
    QuadraticRecoveryReset.CallerFrameAvoids
      (QuadraticScratchViews.resetRefs cells shortLog factorSelection)
      (FirstAccepted.cellRead (Layout.cellRef cells source)) := by
  rcases allowed with rfl | rfl | rfl <;>
    exact resetCallerFrame cells shortLog factorSelection _
      (cellAvoids cells distinct _ .sqrtWideInput (by decide))
      (cellAvoids cells distinct _ .sqrtRoot (by decide))
      (cellAvoids cells distinct _ .sqrtHalf (by decide))
      (cellAvoids cells distinct _ .sqrtOutput (by decide))

/-- One persistent factor-selector cell is framed by the reset. -/
private lemma factorResetFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (factorSelection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N))
    (separation :
      QuadraticCheckSeparation.FactorSeparation cells factorSelection)
    (factor : QuadraticCheckSeparation.FactorCell) :
    QuadraticRecoveryReset.CallerFrameAvoids
      (QuadraticScratchViews.resetRefs cells shortLog factorSelection)
      (QuadraticCheckSeparation.factorInput factorSelection factor) :=
  resetCallerFrame cells shortLog factorSelection _
    (separation.avoidsQuadratic factor .sqrtWideInput)
    (separation.avoidsQuadratic factor .sqrtRoot)
    (separation.avoidsQuadratic factor .sqrtHalf)
    (separation.avoidsQuadratic factor .sqrtOutput)

/-- Full guarded separation follows from the three physical certificates. -/
lemma guardedSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortSelection : FirstAccepted.Direct.Refs ctx
      (QuadraticScratchLayout.ShortWidth N))
    (shortSeparation : ShortSelectionSeparation cells shortSelection)
    (factorSelection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N))
    (factorSeparation :
      QuadraticCheckSeparation.FactorSeparation cells factorSelection) :
    QuadraticRecoveryGuarded.Separation
      (QuadraticScratchViews.guardedRefs cells shortSelection factorSelection) := by
  let shortLog := FirstAccepted.cellRead shortSelection.selected
  let quadratic := QuadraticScratchViews.resetRefs cells shortLog factorSelection
  have sourceFrame (source : QuadraticCheckSeparation.FactorCell) :
      QuadraticRecoveryReset.CallerFrameAvoids quadratic
        (QuadraticCheckSeparation.factorInput factorSelection source) :=
    factorResetFrame cells shortLog factorSelection factorSeparation source
  refine ⟨resetSeparation cells distinct shortLog factorSelection,
    QuadraticRecoverySeparation.recoverySeparation cells distinct shortLog
      shortSeparation.selectedAvoidsQuadratic factorSelection factorSeparation,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact resetCallerFrame cells shortLog factorSelection _
      (shortSeparation.acceptedAvoidsQuadratic .sqrtWideInput)
      (shortSeparation.acceptedAvoidsQuadratic .sqrtRoot)
      (shortSeparation.acceptedAvoidsQuadratic .sqrtHalf)
      (shortSeparation.acceptedAvoidsQuadratic .sqrtOutput)
  · exact resetCallerFrame cells shortLog factorSelection _
      (shortSeparation.selectedAvoidsQuadratic .sqrtWideInput)
      (shortSeparation.selectedAvoidsQuadratic .sqrtRoot)
      (shortSeparation.selectedAvoidsQuadratic .sqrtHalf)
      (shortSeparation.selectedAvoidsQuadratic .sqrtOutput)
  · exact constantResetFrame cells distinct shortLog factorSelection .modulus
      (Or.inr (Or.inr rfl))
  · exact constantResetFrame cells distinct shortLog factorSelection .one
      (Or.inl rfl)
  · exact constantResetFrame cells distinct shortLog factorSelection .modulus
      (Or.inr (Or.inr rfl))
  · exact constantResetFrame cells distinct shortLog factorSelection .zero
      (Or.inr (Or.inl rfl))
  · exact constantResetFrame cells distinct shortLog factorSelection .one
      (Or.inl rfl)
  · exact constantResetFrame cells distinct shortLog factorSelection .modulus
      (Or.inr (Or.inr rfl))
  · exact constantResetFrame cells distinct shortLog factorSelection .zero
      (Or.inr (Or.inl rfl))
  · exact sourceFrame .accepted
  · exact sourceFrame .selected

end

end QuadraticGuardSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
