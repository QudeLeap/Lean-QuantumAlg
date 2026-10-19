/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Transport
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Read

/-!
# Actual initialization of heterogeneous lexical cells

Initialization states the value stored in every actual cell. Lexical workspace
entry initializes its new head and preserves the values of all existing cells.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace.Cells

/-- Every cell contains the deterministic initial encoding of its declared shape. -/
def Initialized {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes) (store : Store ctx) : Prop :=
  match cells with
  | .nil => True
  | .cons head tail =>
      store.read (.storage head.ref.toCStorageRef) = CShape.initialValue _ ∧
      tail.Initialized store

/-- Every indexed member of an initialized collection has its shape's initial value. -/
lemma workspaceCells_cellAt_initialized {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes) (store : Store ctx)
    (initialized : cells.Initialized store) (index : Fin shapes.length) :
    store.read (.storage (cellAt cells index).ref.toCStorageRef) =
      CShape.initialValue (shapes.get index) := by
  induction cells with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      exact Fin.cases initialized.1
        (fun tailIndex => inductionHypothesis initialized.2 tailIndex) index

private lemma initialized_cell_cast {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {first second : CShape} (same : first = second) (cell : Cell ctx first) (store : Store ctx)
    (initialized : store.read (.storage cell.ref.toCStorageRef) = CShape.initialValue first) :
    store.read (.storage (same ▸ cell).ref.toCStorageRef) = CShape.initialValue second := by
  cases same
  exact initialized

/-- Dependent layout lookup preserves the actual initial value at every declared index. -/
lemma workspaceCells_refAt_initialized {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {count : Nat} (shape : Fin count → CShape) (cells : Cells ctx (List.ofFn shape))
    (store : Store ctx) (initialized : cells.Initialized store) (index : Fin count) :
    store.read (.storage (refAt shape cells index).toCStorageRef) =
      CShape.initialValue (shape index) := by
  unfold refAt cellAtOfFn
  apply initialized_cell_cast
  exact workspaceCells_cellAt_initialized cells store initialized _

/-- Actual workspace entry retains the initial values of every existing cell. -/
lemma workspaceCells_initialized_pushWorkspace {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shapes : List CShape} (cells : Cells ctx shapes) (store : Store ctx)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (initialized : cells.Initialized store) :
    (cells.underWorkspace key shape fresh).Initialized (store.pushWorkspace key shape fresh) := by
  induction cells with
  | nil => trivial
  | cons head tail inductionHypothesis =>
      refine ⟨?_, inductionHypothesis initialized.2⟩
      exact (Store.read_pushWorkspace_underWorkspace store key shape fresh
        (.storage head.ref.toCStorageRef)).trans initialized.1

/-- A fresh initialized head joins the initialized cells inherited through workspace entry. -/
lemma workspaceCells_initialized_extend {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shapes : List CShape} (cells : Cells ctx shapes) (store : Store ctx)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (initialized : cells.Initialized store) :
    Initialized
      (.cons { ref := CWriteRef.workspaceHead ctx key shape fresh, role := rfl }
        (cells.underWorkspace key shape fresh)) (store.pushWorkspace key shape fresh) := by
  exact ⟨Store.read_pushWorkspace_head store key shape fresh,
    workspaceCells_initialized_pushWorkspace cells store key shape fresh initialized⟩

/-- Agreement of actual transported reads preserves initialization of the transported cells. -/
lemma workspaceCells_initialized_transport {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} {shapes : List CShape}
    (transport : Transport outer inner) (cells : Cells outer shapes)
    {source : Store outer} {before : Store inner} (reads : transport.ReadsAs source before)
    (initialized : cells.Initialized source) :
    (transportCells transport cells).Initialized before := by
  induction cells with
  | nil => trivial
  | cons head tail inductionHypothesis =>
      exact ⟨(reads (.storage head.ref.toCStorageRef)).trans initialized.1,
        inductionHypothesis initialized.2⟩

end QuantumAlg.Execution.ClassicalWorkspace.Cells
