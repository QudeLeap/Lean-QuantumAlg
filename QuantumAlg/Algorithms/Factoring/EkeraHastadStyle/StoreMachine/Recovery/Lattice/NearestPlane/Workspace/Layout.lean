/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.State.Workspace.Layout

/-!
# Three-stage nearest-plane scratch workspace inventory

The second-coordinate phase has the largest local footprint.  The third and
first phases reuse compatible cells; only the third quotient receives one
extra cell because both later phases must preserve it.  The second quotient is
also excluded from the final phase view, while the final quotient reuses a
second-only word.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeNearestPlaneScratchWorkspaceLayout

open Execution

noncomputable section

/-- Common raw-word width of all three nearest-plane phases. -/
abbrev Width (N : Nat) : Nat := LatticePairStateWorkspaceLayout.Width N

/-- Every physical cell in the reusable three-stage scratch package. -/
inductive Cell where
  | crossFirst | crossSecond | crossThird
  | crossProductLeft | crossProductRight | dotProduct
  | g11 | g21 | targetDotSecond | targetDotFirst
  | numerator | numeratorProduct | denominator
  | divisionMagnitude | divisionNegative
  | divisionWideNumerator | divisionWideDenominator
  | divisionQuotientRemainder | secondOutput | reduceProduct | thirdOutput
deriving DecidableEq

instance : Fintype Cell :=
  Fintype.ofList
    [.crossFirst, .crossSecond, .crossThird,
      .crossProductLeft, .crossProductRight, .dotProduct,
      .g11, .g21, .targetDotSecond, .targetDotFirst,
      .numerator, .numeratorProduct, .denominator,
      .divisionMagnitude, .divisionNegative,
      .divisionWideNumerator, .divisionWideDenominator,
      .divisionQuotientRemainder, .secondOutput, .reduceProduct, .thirdOutput]
    (by
      intro cell
      cases cell <;> simp)

/-- Stable heterogeneous allocation order of the nearest-plane scratch. -/
@[implicit_reducible] def shapes (N : Nat) : List CShape :=
  [.unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N), .bit,
    .unsignedWord (Width N + 1), .unsignedWord (Width N + 1),
    .product (.unsignedWord (Width N + 1)) (.unsignedWord (Width N + 1)),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N)]

/-- Heterogeneous storage for one reusable nearest-plane scratch package. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  ClassicalWorkspace.Cells ctx (shapes N)

/-- Stable numeric index of one named nearest-plane cell. -/
@[implicit_reducible] def cellIndex (N : Nat) : Cell → Fin (shapes N).length
  | .crossFirst => ⟨0, by simp [shapes]⟩
  | .crossSecond => ⟨1, by simp [shapes]⟩
  | .crossThird => ⟨2, by simp [shapes]⟩
  | .crossProductLeft => ⟨3, by simp [shapes]⟩
  | .crossProductRight => ⟨4, by simp [shapes]⟩
  | .dotProduct => ⟨5, by simp [shapes]⟩
  | .g11 => ⟨6, by simp [shapes]⟩
  | .g21 => ⟨7, by simp [shapes]⟩
  | .targetDotSecond => ⟨8, by simp [shapes]⟩
  | .targetDotFirst => ⟨9, by simp [shapes]⟩
  | .numerator => ⟨10, by simp [shapes]⟩
  | .numeratorProduct => ⟨11, by simp [shapes]⟩
  | .denominator => ⟨12, by simp [shapes]⟩
  | .divisionMagnitude => ⟨13, by simp [shapes]⟩
  | .divisionNegative => ⟨14, by simp [shapes]⟩
  | .divisionWideNumerator => ⟨15, by simp [shapes]⟩
  | .divisionWideDenominator => ⟨16, by simp [shapes]⟩
  | .divisionQuotientRemainder => ⟨17, by simp [shapes]⟩
  | .secondOutput => ⟨18, by simp [shapes]⟩
  | .reduceProduct => ⟨19, by simp [shapes]⟩
  | .thirdOutput => ⟨20, by simp [shapes]⟩

/-- Exact runtime shape of one nearest-plane scratch cell. -/
@[implicit_reducible] def cellShape (N : Nat) (cell : Cell) : CShape :=
  (shapes N).get (cellIndex N cell)

/-- Resolve one named scratch cell to its typed writable reference. -/
def cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) : CWriteRef ctx (cellShape N cell) :=
  (ClassicalWorkspace.cellAt cells (cellIndex N cell)).ref

/-- Every named nearest-plane scratch cell is workspace-owned. -/
lemma cellRef_role {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :
    (cellRef cells cell).toCStorageRef.role = .workspace := by
  exact (ClassicalWorkspace.cellAt cells (cellIndex N cell)).role

/-- The named reference and numeric index have the same physical key. -/
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

/-- Distinct allocation cells give an injective named key projection. -/
lemma cellRef_key_injective {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Cells ctx N) (distinct : cells.Distinct) :
    Function.Injective (fun cell => (cellRef cells cell).toCStorageRef.key) := by
  intro left right equal
  apply cellIndex_injective N
  apply ClassicalWorkspace.workspaceCells_cellAt_key_injective cells distinct
  simpa only [cellRef_key] using equal

end

end LatticeNearestPlaneScratchWorkspaceLayout
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
