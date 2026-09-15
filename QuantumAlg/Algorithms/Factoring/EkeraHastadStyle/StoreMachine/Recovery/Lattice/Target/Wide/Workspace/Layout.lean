/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.State.Workspace.Layout

/-!
# Wide-target scratch workspace inventory

The two decoded target preimages and the two centered-coordinate loaders run
before fixed-fuel LLL.  This module names their eight phase-local cells.  The
three target outputs remain in the persistent pair-state allocation.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeWideTargetWorkspaceLayout

open Execution

noncomputable section

/-- Common raw-word width of the wide target and fixed-fuel state. -/
abbrev Width (N : Nat) : Nat := LatticePairStateWorkspaceLayout.Width N

/-- Every phase-local cell used while materializing the wide target. -/
inductive Cell where
  | firstScaled | secondScaled
  | firstScratch | firstIsZero | firstBelowHalf
  | secondScratch | secondIsZero | secondBelowHalf
deriving DecidableEq

instance : Fintype Cell :=
  Fintype.ofList
    [.firstScaled, .secondScaled,
      .firstScratch, .firstIsZero, .firstBelowHalf,
      .secondScratch, .secondIsZero, .secondBelowHalf]
    (by
      intro cell
      cases cell <;> simp)

/-- Stable heterogeneous allocation order of the wide-target scratch. -/
@[implicit_reducible] def shapes (N : Nat) : List CShape :=
  [.unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .bit, .bit,
    .unsignedWord (Width N), .bit, .bit]

/-- Heterogeneous storage for the wide-target scratch. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  ClassicalWorkspace.Cells ctx (shapes N)

/-- Stable numeric index of one named scratch cell. -/
@[implicit_reducible] def cellIndex (N : Nat) : Cell → Fin (shapes N).length
  | .firstScaled => ⟨0, by simp [shapes]⟩
  | .secondScaled => ⟨1, by simp [shapes]⟩
  | .firstScratch => ⟨2, by simp [shapes]⟩
  | .firstIsZero => ⟨3, by simp [shapes]⟩
  | .firstBelowHalf => ⟨4, by simp [shapes]⟩
  | .secondScratch => ⟨5, by simp [shapes]⟩
  | .secondIsZero => ⟨6, by simp [shapes]⟩
  | .secondBelowHalf => ⟨7, by simp [shapes]⟩

/-- Exact runtime shape of one wide-target scratch cell. -/
@[implicit_reducible] def cellShape (N : Nat) (cell : Cell) : CShape :=
  (shapes N).get (cellIndex N cell)

/-- Resolve one named scratch cell to its typed writable reference. -/
def cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) : CWriteRef ctx (cellShape N cell) :=
  (ClassicalWorkspace.cellAt cells (cellIndex N cell)).ref

/-- Every named wide-target scratch cell is workspace-owned. -/
theorem cellRef_role {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :
    (cellRef cells cell).toCStorageRef.role = .workspace := by
  exact (ClassicalWorkspace.cellAt cells (cellIndex N cell)).role

/-- The named reference and numeric index have the same physical key. -/
theorem cellRef_key {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :
    (cellRef cells cell).toCStorageRef.key =
      (ClassicalWorkspace.cellAt cells (cellIndex N cell)).ref.toCStorageRef.key := by
  rfl

private theorem cellIndex_zero_injective : Function.Injective (cellIndex 0) := by
  decide

private theorem cellIndex_val_eq (N M : Nat) (cell : Cell) :
    (cellIndex N cell).val = (cellIndex M cell).val := by
  cases cell <;> rfl

/-- The stable numeric index is injective on named cells. -/
theorem cellIndex_injective (N : Nat) : Function.Injective (cellIndex N) := by
  intro left right equal
  apply cellIndex_zero_injective
  apply Fin.ext
  calc
    (cellIndex 0 left).val = (cellIndex N left).val := cellIndex_val_eq 0 N left
    _ = (cellIndex N right).val := congrArg Fin.val equal
    _ = (cellIndex 0 right).val := cellIndex_val_eq N 0 right

/-- Distinct allocation cells give an injective named key projection. -/
theorem cellRef_key_injective {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Cells ctx N) (distinct : cells.Distinct) :
    Function.Injective (fun cell => (cellRef cells cell).toCStorageRef.key) := by
  intro left right equal
  apply cellIndex_injective N
  apply ClassicalWorkspace.workspaceCells_cellAt_key_injective cells distinct
  simpa only [cellRef_key] using equal

end

end LatticeWideTargetWorkspaceLayout
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
