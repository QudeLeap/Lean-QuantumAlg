/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.State.Workspace.Layout

/-!
# Fixed-fuel LLL scratch workspace inventory

The seven Gram cells are shared by both LLL phases.  The remaining cells are
the maximum live second-phase footprint; the mutually exclusive first phase
reuses compatible cells through a later view.  This avoids summing both branch
allocations while retaining distinct storage inside either active branch.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeFixedFuelScratchWorkspaceLayout

open Execution

noncomputable section

/-- Common raw-word width of the fixed-fuel LLL machine. -/
abbrev Width (N : Nat) : Nat := LatticePairStateWorkspaceLayout.Width N

/-- Every physical cell in the reusable fixed-fuel scratch package. -/
inductive Cell where
  | metricG11 | metricG21 | metricG31 | metricG22 | metricG32 | metricG33
  | metricProduct
  | refreshG21Product | refreshG32Product
  | nu32 | d32 | reductionInputsProduct
  | division32Magnitude | division32Negative
  | division32WideNumerator | division32WideDenominator | division32Division
  | division32Output
  | division31Magnitude | division31Negative
  | division31WideNumerator | division31WideDenominator | division31Division
  | division31Output | reduceProduct
  | area12ProductLeft | area12ProductRight
  | area12CrossFirst | area12CrossSecond | area12CrossThird
  | area12Result | area12NormProduct
  | area13ProductLeft | area13ProductRight
  | area13CrossFirst | area13CrossSecond | area13CrossThird
  | area13Result | area13NormProduct
  | lovaszDoubled | lovaszPasses | swapScratch
deriving DecidableEq

instance : Fintype Cell :=
  Fintype.ofList
    [.metricG11, .metricG21, .metricG31, .metricG22, .metricG32, .metricG33,
      .metricProduct,
      .refreshG21Product, .refreshG32Product,
      .nu32, .d32, .reductionInputsProduct,
      .division32Magnitude, .division32Negative,
      .division32WideNumerator, .division32WideDenominator, .division32Division,
      .division32Output,
      .division31Magnitude, .division31Negative,
      .division31WideNumerator, .division31WideDenominator, .division31Division,
      .division31Output, .reduceProduct,
      .area12ProductLeft, .area12ProductRight,
      .area12CrossFirst, .area12CrossSecond, .area12CrossThird,
      .area12Result, .area12NormProduct,
      .area13ProductLeft, .area13ProductRight,
      .area13CrossFirst, .area13CrossSecond, .area13CrossThird,
      .area13Result, .area13NormProduct,
      .lovaszDoubled, .lovaszPasses, .swapScratch]
    (by
      intro cell
      cases cell <;> simp)

/-- Stable heterogeneous allocation order of the fixed-fuel scratch. -/
@[implicit_reducible] def shapes (N : Nat) : List CShape :=
  [.unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .bit,
    .unsignedWord (Width N + 1), .unsignedWord (Width N + 1),
    .product (.unsignedWord (Width N + 1)) (.unsignedWord (Width N + 1)),
    .unsignedWord (Width N), .unsignedWord (Width N), .bit,
    .unsignedWord (Width N + 1), .unsignedWord (Width N + 1),
    .product (.unsignedWord (Width N + 1)) (.unsignedWord (Width N + 1)),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .unsignedWord (Width N),
    .unsignedWord (Width N), .bit, .unsignedWord (Width N)]

/-- Heterogeneous storage for one reusable fixed-fuel scratch package. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  ClassicalWorkspace.Cells ctx (shapes N)

/-- Stable numeric index of one named fixed-fuel cell. -/
@[implicit_reducible] def cellIndex (N : Nat) : Cell → Fin (shapes N).length
  | .metricG11 => ⟨0, by simp [shapes]⟩
  | .metricG21 => ⟨1, by simp [shapes]⟩
  | .metricG31 => ⟨2, by simp [shapes]⟩
  | .metricG22 => ⟨3, by simp [shapes]⟩
  | .metricG32 => ⟨4, by simp [shapes]⟩
  | .metricG33 => ⟨5, by simp [shapes]⟩
  | .metricProduct => ⟨6, by simp [shapes]⟩
  | .refreshG21Product => ⟨7, by simp [shapes]⟩
  | .refreshG32Product => ⟨8, by simp [shapes]⟩
  | .nu32 => ⟨9, by simp [shapes]⟩
  | .d32 => ⟨10, by simp [shapes]⟩
  | .reductionInputsProduct => ⟨11, by simp [shapes]⟩
  | .division32Magnitude => ⟨12, by simp [shapes]⟩
  | .division32Negative => ⟨13, by simp [shapes]⟩
  | .division32WideNumerator => ⟨14, by simp [shapes]⟩
  | .division32WideDenominator => ⟨15, by simp [shapes]⟩
  | .division32Division => ⟨16, by simp [shapes]⟩
  | .division32Output => ⟨17, by simp [shapes]⟩
  | .division31Magnitude => ⟨18, by simp [shapes]⟩
  | .division31Negative => ⟨19, by simp [shapes]⟩
  | .division31WideNumerator => ⟨20, by simp [shapes]⟩
  | .division31WideDenominator => ⟨21, by simp [shapes]⟩
  | .division31Division => ⟨22, by simp [shapes]⟩
  | .division31Output => ⟨23, by simp [shapes]⟩
  | .reduceProduct => ⟨24, by simp [shapes]⟩
  | .area12ProductLeft => ⟨25, by simp [shapes]⟩
  | .area12ProductRight => ⟨26, by simp [shapes]⟩
  | .area12CrossFirst => ⟨27, by simp [shapes]⟩
  | .area12CrossSecond => ⟨28, by simp [shapes]⟩
  | .area12CrossThird => ⟨29, by simp [shapes]⟩
  | .area12Result => ⟨30, by simp [shapes]⟩
  | .area12NormProduct => ⟨31, by simp [shapes]⟩
  | .area13ProductLeft => ⟨32, by simp [shapes]⟩
  | .area13ProductRight => ⟨33, by simp [shapes]⟩
  | .area13CrossFirst => ⟨34, by simp [shapes]⟩
  | .area13CrossSecond => ⟨35, by simp [shapes]⟩
  | .area13CrossThird => ⟨36, by simp [shapes]⟩
  | .area13Result => ⟨37, by simp [shapes]⟩
  | .area13NormProduct => ⟨38, by simp [shapes]⟩
  | .lovaszDoubled => ⟨39, by simp [shapes]⟩
  | .lovaszPasses => ⟨40, by simp [shapes]⟩
  | .swapScratch => ⟨41, by simp [shapes]⟩

/-- Exact runtime shape of one fixed-fuel scratch cell. -/
@[implicit_reducible] def cellShape (N : Nat) (cell : Cell) : CShape :=
  (shapes N).get (cellIndex N cell)

/-- Resolve one named scratch cell to its typed writable reference. -/
def cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) : CWriteRef ctx (cellShape N cell) :=
  (ClassicalWorkspace.cellAt cells (cellIndex N cell)).ref

/-- Every named fixed-fuel scratch cell is workspace-owned. -/
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

end LatticeFixedFuelScratchWorkspaceLayout
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
