/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells

/-!
# Actual workspace-cell freshness and distinctness under lexical allocation
-/

namespace QuantumAlg.Execution.ClassicalWorkspace.Cells

theorem workspaceCells_storageKey_mem_keys {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shape : CShape} (ref : CStorageRef ctx shape) :
    ref.key ∈ ctx.keys := by
  rw [RuntimeCtx.keys, List.mem_map]
  exact ⟨_, ref.present, rfl⟩

theorem workspaceCells_underWorkspace_avoidsKey {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (avoided : StorageKey)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (avoids : cells.AvoidsKey avoided) :
    (cells.underWorkspace key shape fresh).AvoidsKey avoided := by
  induction cells with
  | nil => trivial
  | cons head tail tailIH =>
      rcases avoids with ⟨headAvoids, tailAvoids⟩
      refine ⟨?_, tailIH tailAvoids⟩
      simpa only [Cells.underWorkspace, CWriteRef.underWorkspace,
        CStorageRef.underWorkspace] using headAvoids

theorem workspaceCells_underWorkspace_avoids_fresh {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (cells.underWorkspace key shape fresh).AvoidsKey key := by
  induction cells with
  | nil => trivial
  | cons head tail tailIH =>
      refine ⟨?_, tailIH⟩
      change head.ref.toCStorageRef.key ≠ key
      intro equal
      apply fresh
      rw [← equal]
      exact workspaceCells_storageKey_mem_keys head.ref.toCStorageRef

theorem workspaceCells_underWorkspace_distinct {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (distinct : cells.Distinct)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (cells.underWorkspace key shape fresh).Distinct := by
  induction cells with
  | nil => trivial
  | cons head tail tailIH =>
      rcases distinct with ⟨headDistinct, tailDistinct⟩
      refine ⟨?_, tailIH tailDistinct⟩
      exact workspaceCells_underWorkspace_avoidsKey tail head.ref.toCStorageRef.key
        key shape fresh headDistinct

theorem workspaceCells_cons_distinct {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shape : CShape} {shapes : List CShape}
    (head : Cell ctx shape) (tail : Cells ctx shapes)
    (tailAvoids : tail.AvoidsKey head.ref.toCStorageRef.key)
    (tailDistinct : tail.Distinct) :
    (Cells.cons head tail).Distinct :=
  ⟨tailAvoids, tailDistinct⟩


end QuantumAlg.Execution.ClassicalWorkspace.Cells
