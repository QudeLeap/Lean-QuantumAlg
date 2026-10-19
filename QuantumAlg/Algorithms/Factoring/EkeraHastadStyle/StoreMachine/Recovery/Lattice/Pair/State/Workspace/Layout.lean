/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Layout

/-!
# Persistent pair-recovery workspace inventory

One terminal pair reuses a fixed long-lived state while its LLL and
nearest-plane scratch packages execute.  This module names the two decoded
terminal records, the shared wide basis and target, the two LLL phase latches,
and the saved target.  Phase-local scratch remains in later layout layers.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairStateWorkspaceLayout

open Execution

noncomputable section

/-- Common raw-word width of the fixed-fuel LLL and nearest-plane state. -/
abbrev Width (N : Nat) : Nat := LatticeWideLllMachine.Width N

/-- Every long-lived mutable cell shared by one terminal-pair invocation. -/
inductive Cell where
  | firstFull | firstScratch | firstJ | firstK
  | secondFull | secondScratch | secondJ | secondK
  | basis11 | basis12 | basis13
  | basis21 | basis22 | basis23
  | basis31 | basis32 | basis33
  | targetFirst | targetSecond | targetThird
  | secondPhase | done
  | savedTargetFirst | savedTargetSecond | savedTargetThird
deriving DecidableEq

instance : Fintype Cell :=
  Fintype.ofList
    [.firstFull, .firstScratch, .firstJ, .firstK,
      .secondFull, .secondScratch, .secondJ, .secondK,
      .basis11, .basis12, .basis13,
      .basis21, .basis22, .basis23,
      .basis31, .basis32, .basis33,
      .targetFirst, .targetSecond, .targetThird,
      .secondPhase, .done,
      .savedTargetFirst, .savedTargetSecond, .savedTargetThird]
    (by
      intro cell
      cases cell <;> simp)

/-- Stable heterogeneous allocation order of the persistent pair state. -/
@[implicit_reducible] def shapes (N : Nat) : List CShape :=
  [.unsignedWord (measurementBits N), .unsignedWord (measurementBits N),
    .unsignedWord (BatchMachine.JWidth N), .unsignedWord (BatchMachine.KWidth N),
    .unsignedWord (measurementBits N), .unsignedWord (measurementBits N),
    .unsignedWord (BatchMachine.JWidth N), .unsignedWord (BatchMachine.KWidth N),
    .unsignedWord (Width N), .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N), .unsignedWord (Width N),
    .bit, .bit,
    .unsignedWord (Width N), .unsignedWord (Width N), .unsignedWord (Width N)]

/-- Heterogeneous storage for the persistent pair state. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  ClassicalWorkspace.Cells ctx (shapes N)

/-- Stable numeric index of one named persistent cell. -/
@[implicit_reducible] def cellIndex (N : Nat) : Cell → Fin (shapes N).length
  | .firstFull => ⟨0, by simp [shapes]⟩
  | .firstScratch => ⟨1, by simp [shapes]⟩
  | .firstJ => ⟨2, by simp [shapes]⟩
  | .firstK => ⟨3, by simp [shapes]⟩
  | .secondFull => ⟨4, by simp [shapes]⟩
  | .secondScratch => ⟨5, by simp [shapes]⟩
  | .secondJ => ⟨6, by simp [shapes]⟩
  | .secondK => ⟨7, by simp [shapes]⟩
  | .basis11 => ⟨8, by simp [shapes]⟩
  | .basis12 => ⟨9, by simp [shapes]⟩
  | .basis13 => ⟨10, by simp [shapes]⟩
  | .basis21 => ⟨11, by simp [shapes]⟩
  | .basis22 => ⟨12, by simp [shapes]⟩
  | .basis23 => ⟨13, by simp [shapes]⟩
  | .basis31 => ⟨14, by simp [shapes]⟩
  | .basis32 => ⟨15, by simp [shapes]⟩
  | .basis33 => ⟨16, by simp [shapes]⟩
  | .targetFirst => ⟨17, by simp [shapes]⟩
  | .targetSecond => ⟨18, by simp [shapes]⟩
  | .targetThird => ⟨19, by simp [shapes]⟩
  | .secondPhase => ⟨20, by simp [shapes]⟩
  | .done => ⟨21, by simp [shapes]⟩
  | .savedTargetFirst => ⟨22, by simp [shapes]⟩
  | .savedTargetSecond => ⟨23, by simp [shapes]⟩
  | .savedTargetThird => ⟨24, by simp [shapes]⟩

/-- Exact runtime shape of one persistent pair-state cell. -/
@[implicit_reducible] def cellShape (N : Nat) (cell : Cell) : CShape :=
  (shapes N).get (cellIndex N cell)

/-- Resolve one named cell to its typed writable reference. -/
def cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) : CWriteRef ctx (cellShape N cell) :=
  (ClassicalWorkspace.cellAt cells (cellIndex N cell)).ref

/-- Every persistent pair-state cell is workspace-owned. -/
lemma cellRef_role {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :
    (cellRef cells cell).toCStorageRef.role = .workspace := by
  exact (ClassicalWorkspace.cellAt cells (cellIndex N cell)).role

/-- The named reference and numeric layout index have the same physical key. -/
lemma cellRef_key {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :
    (cellRef cells cell).toCStorageRef.key =
      (ClassicalWorkspace.cellAt cells (cellIndex N cell)).ref.toCStorageRef.key := by
  rfl

private lemma cellIndex_zero_injective : Function.Injective (cellIndex 0) := by
  decide

private lemma cellIndex_val_eq (N M : Nat) (cell : Cell) :
    (cellIndex N cell).val = (cellIndex M cell).val := by
  cases cell <;> rfl

/-- The stable numeric index is injective on named cells. -/
lemma cellIndex_injective (N : Nat) : Function.Injective (cellIndex N) := by
  intro left right equal
  apply cellIndex_zero_injective
  apply Fin.ext
  calc
    (cellIndex 0 left).val = (cellIndex N left).val := cellIndex_val_eq 0 N left
    _ = (cellIndex N right).val := congrArg Fin.val equal
    _ = (cellIndex 0 right).val := cellIndex_val_eq N 0 right

/-- Distinct allocation cells give an injective named storage-key projection. -/
lemma cellRef_key_injective {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Cells ctx N) (distinct : cells.Distinct) :
    Function.Injective (fun cell => (cellRef cells cell).toCStorageRef.key) := by
  intro left right equal
  apply cellIndex_injective N
  apply ClassicalWorkspace.workspaceCells_cellAt_key_injective cells distinct
  simpa only [cellRef_key] using equal

end

end LatticePairStateWorkspaceLayout
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
