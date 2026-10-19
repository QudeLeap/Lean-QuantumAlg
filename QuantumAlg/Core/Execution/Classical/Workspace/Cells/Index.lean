/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Cells
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells

/-!
# Dependent indexing and physical key separation of actual workspace cells
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

/-- Retrieve one typed cell from a heterogeneous workspace list. -/
public def cellAt {kind : ProblemKind} {ctx : RuntimeCtx kind} :
    {shapes : List CShape} → (cells : Cells ctx shapes) →
      (index : Fin shapes.length) →
        Cell ctx (shapes.get index)
  | [], .nil, index => Fin.elim0 index
  | _shape :: _shapes, .cons head tail, index =>
      Fin.cases head (fun tailIndex => cellAt tail tailIndex) index

/-- Retrieve a cell from a layout described by one dependent shape function. -/
public def cellAtOfFn {kind : ProblemKind} {ctx : RuntimeCtx kind} {count : Nat}
    (shape : Fin count → CShape)
    (cells : Cells ctx (List.ofFn shape)) (index : Fin count) :
    Cell ctx (shape index) := by
  let listIndex : Fin (List.ofFn shape).length := Fin.cast (by simp) index
  have shapeEq : (List.ofFn shape).get listIndex = shape index := by
    rw [List.get_ofFn]
    congr 1
  exact shapeEq ▸ cellAt cells listIndex

/-- Writable reference at one dependent layout index. -/
public def refAt {kind : ProblemKind} {ctx : RuntimeCtx kind} {count : Nat}
    (shape : Fin count → CShape)
    (cells : Cells ctx (List.ofFn shape)) (index : Fin count) :
    CWriteRef ctx (shape index) :=
  (cellAtOfFn shape cells index).ref

/-- Every reference retrieved from an allocated layout is workspace-owned. -/
public lemma workspaceCells_refAt_role {kind : ProblemKind} {ctx : RuntimeCtx kind} {count : Nat}
    (shape : Fin count → CShape)
    (cells : Cells ctx (List.ofFn shape)) (index : Fin count) :
  (refAt shape cells index).toCStorageRef.role = .workspace :=
  (cellAtOfFn shape cells index).role

/-- A retrieved cell inherits avoidance of one key from the complete list. -/
public lemma workspaceCells_cellAt_key_ne_of_avoids {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (key : StorageKey)
    (avoids : cells.AvoidsKey key) (index : Fin shapes.length) :
    (cellAt cells index).ref.toCStorageRef.key ≠ key := by
  induction cells with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      rcases avoids with ⟨headAvoids, tailAvoids⟩
      exact Fin.cases headAvoids
        (fun tailIndex => inductionHypothesis tailAvoids tailIndex) index

/-- The key of every indexed cell occurs in the heterogeneous key list. -/
public lemma workspaceCells_cellAt_key_mem_keys {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (index : Fin shapes.length) :
    (cellAt cells index).ref.toCStorageRef.key ∈ cells.keys := by
  induction cells with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · change head.ref.toCStorageRef.key ∈
          head.ref.toCStorageRef.key :: tail.keys
        exact List.mem_cons_self
      · change (cellAt tail tailIndex).ref.toCStorageRef.key ∈
          head.ref.toCStorageRef.key :: tail.keys
        exact List.mem_cons_of_mem _ (inductionHypothesis tailIndex)

/-- Distinct heterogeneous cells have an injective indexed key projection. -/
public lemma workspaceCells_cellAt_key_injective {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (distinct : cells.Distinct) :
    Function.Injective
      (fun index => (cellAt cells index).ref.toCStorageRef.key) := by
  induction cells with
  | nil =>
      intro left
      exact Fin.elim0 left
  | cons head tail inductionHypothesis =>
      rcases distinct with ⟨tailAvoids, tailDistinct⟩
      intro left
      refine Fin.cases ?_ (fun leftTail => ?_) left
      · intro right
        refine Fin.cases ?_ (fun rightTail equal => ?_) right
        · intro _equal
          rfl
        · exact (workspaceCells_cellAt_key_ne_of_avoids tail
            head.ref.toCStorageRef.key tailAvoids rightTail equal.symm).elim
      · intro right
        refine Fin.cases ?_ (fun rightTail equal => ?_) right
        · intro equal
          exact (workspaceCells_cellAt_key_ne_of_avoids tail
            head.ref.toCStorageRef.key tailAvoids leftTail equal).elim
        · exact congrArg Fin.succ
            (inductionHypothesis tailDistinct equal)

end QuantumAlg.Execution.ClassicalWorkspace
