/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Typed collections of actual classical workspace references

These structural views retain the actual storage identities and ownership roles.
They provide heterogeneous indexing and transport through the existing lexical
workspace instruction. Execution and storage remain owned by the single Circuit
interpreter and Store.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

/-- One internally allocated workspace cell together with its ownership fact. -/
structure Cell {kind : ProblemKind} (ctx : RuntimeCtx kind) (shape : CShape) where
  /-- The writable reference for this allocated workspace cell. -/
  ref : CWriteRef ctx shape
  role : ref.toCStorageRef.role = .workspace

/-- A heterogeneous collection of live lexical workspaces. -/
inductive Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    List CShape → Type where
  | nil : Cells ctx []
  | cons {shape : CShape} {shapes : List CShape}
      (head : Cell ctx shape) (tail : Cells ctx shapes) :
      Cells ctx (shape :: shapes)

namespace Cells

/-- Head cell of a nonempty heterogeneous workspace list. -/
def head {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    {shapes : List CShape} : Cells ctx (shape :: shapes) → Cell ctx shape
  | .cons first _ => first

/-- Tail cells of a nonempty heterogeneous workspace list. -/
def tail {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    {shapes : List CShape} : Cells ctx (shape :: shapes) → Cells ctx shapes
  | .cons _ remaining => remaining

/-- Lift every live lexical cell through one further workspace allocation. -/
def underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    Cells (ctx.addWorkspace key shape fresh) shapes :=
  match cells with
  | .nil => .nil
  | .cons head tail =>
      .cons
        { ref := head.ref.underWorkspace key shape fresh
          role := by
            change head.ref.toCStorageRef.role = .workspace
            exact head.role }
        (tail.underWorkspace key shape fresh)

/-- Every member of a heterogeneous collection avoids one key. -/
def AvoidsKey {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes)
    (key : StorageKey) : Prop :=
  match cells with
  | .nil => True
  | .cons head tail =>
      head.ref.toCStorageRef.key ≠ key ∧ tail.AvoidsKey key

/-- Storage keys of a heterogeneous collection, in allocation-stack order. -/
def keys {kind : ProblemKind} {ctx : RuntimeCtx kind} {shapes : List CShape} :
    Cells ctx shapes → List StorageKey
  | .nil => []
  | .cons head tail => head.ref.toCStorageRef.key :: tail.keys

theorem workspaceCells_keys_eq_nil {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (cells : Cells ctx []) : cells.keys = [] := by
  cases cells
  rfl

theorem workspaceCells_keys_eq_cons_head_tail {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {shapes : List CShape}
    (cells : Cells ctx (shape :: shapes)) :
    cells.keys = cells.head.ref.toCStorageRef.key :: cells.tail.keys := by
  cases cells
  rfl

/-- The live lexical cells have pairwise distinct storage keys. -/
def Distinct {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes) : Prop :=
  match cells with
  | .nil => True
  | .cons head tail =>
      tail.AvoidsKey head.ref.toCStorageRef.key ∧ tail.Distinct

theorem workspaceCells_avoidsKey_not_mem_keys {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes) (key : StorageKey)
    (avoids : cells.AvoidsKey key) : key ∉ cells.keys := by
  induction cells with
  | nil => simp [keys]
  | cons head tail tailIH =>
      rcases avoids with ⟨headAvoids, tailAvoids⟩
      simp only [keys, List.mem_cons, not_or]
      exact ⟨Ne.symm headAvoids, tailIH tailAvoids⟩

theorem workspaceCells_distinct_keys_nodup {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes)
    (distinct : cells.Distinct) : cells.keys.Nodup := by
  induction cells with
  | nil => exact List.nodup_nil
  | cons head tail tailIH =>
      rcases distinct with ⟨headDistinct, tailDistinct⟩
      exact List.nodup_cons.mpr
        ⟨workspaceCells_avoidsKey_not_mem_keys tail head.ref.toCStorageRef.key headDistinct,
          tailIH tailDistinct⟩


end Cells

end QuantumAlg.Execution.ClassicalWorkspace
