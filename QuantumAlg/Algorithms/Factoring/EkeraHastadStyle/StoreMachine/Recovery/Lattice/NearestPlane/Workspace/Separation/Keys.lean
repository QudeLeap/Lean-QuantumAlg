/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Package
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Views

/-!
# Nearest-plane physical workspace identities
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical
namespace LatticeNearestPlaneScratchWorkspaceSeparation

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

/-- The persistent state and reusable scratch have distinct, disjoint physical cells. -/
structure PhysicalSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N) : Prop where
  stateDistinct : state.Distinct
  scratchDistinct : scratch.Distinct
  stateScratch : ClassicalWorkspace.CrossSeparated state scratch

private theorem storageRead_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

/-- Abbreviation for the local state cell interface. -/
abbrev StateCell := LatticePairStateWorkspaceLayout.Cell

/-- Abbreviation for the local scratch cell interface. -/
abbrev ScratchCell := LatticeNearestPlaneScratchWorkspaceLayout.Cell

/-- Unified physical name for persistent pair state and nearest-plane scratch. -/
abbrev PhysicalCell := StateCell ⊕ ScratchCell

/-- Physical key of one unified nearest-plane cell. -/
def physicalKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : LatticePairStateWorkspaceLayout.Cells ctx N)
    (scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N) :
    PhysicalCell → StorageKey
  | .inl cell =>
      (LatticePairStateWorkspaceLayout.cellRef state cell).toCStorageRef.key
  | .inr cell =>
      (LatticeNearestPlaneScratchWorkspaceLayout.cellRef scratch cell).toCStorageRef.key

/-- Local distinctness and the state-to-nearest cross certificate make the
unified physical key projection injective. -/
theorem physicalKey_injective {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat}
    {state : LatticePairStateWorkspaceLayout.Cells ctx N}
    {scratch : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N}
    (certificates : PhysicalSeparation state scratch) :
    Function.Injective (physicalKey state scratch) := by
  intro left right equal
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          apply congrArg Sum.inl
          apply LatticePairStateWorkspaceLayout.cellRef_key_injective
            state certificates.stateDistinct
          exact equal
      | inr right =>
          exact (certificates.stateScratch.keysNe
            (LatticePairStateWorkspaceLayout.cellIndex N left)
            (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N right)
              equal).elim
  | inr left =>
      cases right with
      | inl right =>
          exact (certificates.stateScratch.keysNe
            (LatticePairStateWorkspaceLayout.cellIndex N right)
            (LatticeNearestPlaneScratchWorkspaceLayout.cellIndex N left)
              equal.symm).elim
      | inr right =>
          apply congrArg Sum.inr
          apply LatticeNearestPlaneScratchWorkspaceLayout.cellRef_key_injective
            scratch certificates.scratchDistinct
          exact equal

end

end LatticeNearestPlaneScratchWorkspaceSeparation
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
