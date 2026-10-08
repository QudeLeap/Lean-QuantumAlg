/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.Accounting.Context
import Mathlib.Logic.Equiv.Defs

/-!
# Actual borrowed classical cells

The borrowed classical interface consists exactly of the cells tagged as
borrowed input, in context entry order. Its shape is the corresponding nested
product of the original cell shapes. Reading this interface traverses the
existing store cells; it does not create another runtime store.

The circuit's allowed allocations and lexical workspace release preserve the
borrowed cell identities, their shapes, and their structural readout. Joint
classical-quantum restoration can therefore compare these actual values with
the borrowed quantum systems and their external reference together.
-/

namespace QuantumAlg

namespace RuntimeEntry

/-- Only classical cells declared as borrowed input enter this interface. -/
@[implicit_reducible]
def borrowedClassicalCells {kind : ProblemKind} : RuntimeEntry kind → List (StorageKey × CShape)
  | .storage key .borrowedInput shape => [(key, shape)]
  | .storage _ .workspace _ => []
  | .storage _ .retained _ => []
  | .storage _ .finalOutput _ => []
  | .borrowedLayout _ _ => []
  | .suppliedLayout _ _ => []
  | .ownedLayout _ _ => []
  | .ownedCopies _ _ => []

end RuntimeEntry

/-- The shaped product of exactly the listed classical cells. -/
@[implicit_reducible]
private def borrowedCellShape : List (StorageKey × CShape) → CShape
  | [] => .unit
  | cell :: rest => .product cell.2 (borrowedCellShape rest)

namespace RuntimeCtx

variable {kind : ProblemKind}

/-- Borrowed classical keys and their actual shapes, in context order. -/
@[implicit_reducible]
def borrowedClassicalCells (ctx : RuntimeCtx kind) : List (StorageKey × CShape) :=
  ctx.entries.flatMap RuntimeEntry.borrowedClassicalCells

/-- A finite structural product containing every borrowed classical value. -/
@[implicit_reducible]
def borrowedClassicalShape (ctx : RuntimeCtx kind) : CShape :=
  borrowedCellShape ctx.borrowedClassicalCells

@[simp] theorem borrowedClassicalCells_empty :
    (RuntimeCtx.empty : RuntimeCtx kind).borrowedClassicalCells = [] := rfl

/-- Supplying another borrowed input extends, rather than hides, the borrowed interface. -/
@[simp] theorem borrowedClassicalCells_addBorrowedInput (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addBorrowedInput key shape fresh).borrowedClassicalCells =
      (key, shape) :: ctx.borrowedClassicalCells := rfl

/-- Lexical work storage does not enter the borrowed classical interface. -/
@[simp] theorem borrowedClassicalCells_addWorkspace (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addWorkspace key shape fresh).borrowedClassicalCells = ctx.borrowedClassicalCells := rfl

/-- Retained result storage does not enter the borrowed classical interface. -/
@[simp] theorem borrowedClassicalCells_addRetained (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addRetained key shape fresh).borrowedClassicalCells = ctx.borrowedClassicalCells := rfl

/-- Dedicated output storage does not retag any borrowed classical cell. -/
@[simp] theorem borrowedClassicalCells_addFinalOutput (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (ctx.addFinalOutput key shape fresh).borrowedClassicalCells = ctx.borrowedClassicalCells := rfl

/-- Borrowed quantum systems add no classical value to this interface. -/
@[simp] theorem borrowedClassicalCells_addBorrowedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addBorrowedLayout key layout fresh disjoint).borrowedClassicalCells =
      ctx.borrowedClassicalCells := rfl

/-- Freshly owned systems add no borrowed classical cell. -/
@[simp] theorem borrowedClassicalCells_addOwnedLayout (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (ctx.addOwnedLayout key layout fresh disjoint).borrowedClassicalCells =
      ctx.borrowedClassicalCells := rfl

/-- An owned bank contributes only its quantum presence marker to the store. -/
@[simp] theorem borrowedClassicalCells_addOwnedCopies (ctx : RuntimeCtx .quantum)
    (key : StorageKey) {copyCount systemsPerCopy : Nat}
    (bank : OwnedCopyBank copyCount systemsPerCopy) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint bank.identities ctx.physicalIdx) :
    (ctx.addOwnedCopies key bank fresh disjoint).borrowedClassicalCells =
      ctx.borrowedClassicalCells := rfl

/-- Equal ordered borrowed cells have the very same structural value shape. -/
theorem borrowedClassicalShape_eq {pre post : RuntimeCtx kind}
    (same : pre.borrowedClassicalCells = post.borrowedClassicalCells) :
    pre.borrowedClassicalShape = post.borrowedClassicalShape :=
  congrArg borrowedCellShape same

end RuntimeCtx

namespace Execution

/-- A head entry contributes its actual value exactly when its role is borrowed input. -/
private def prependBorrowedCell {kind : ProblemKind} (entry : RuntimeEntry kind)
    (tail : List (StorageKey × CShape)) (value : CellValue entry)
    (rest : (borrowedCellShape tail).Value) :
    (borrowedCellShape (entry.borrowedClassicalCells ++ tail)).Value := by
  cases entry with
  | storage key role shape =>
      cases role with
      | borrowedInput => exact .product value rest
      | workspace | retained | finalOutput => exact rest
  | borrowedLayout | suppliedLayout | ownedLayout | ownedCopies => exact rest

/-- Read only borrowed-role cells directly from the existing heterogeneous store. -/
private def readBorrowedCells {kind : ProblemKind} (entries : List (RuntimeEntry kind))
    (cells : Cells entries) :
    (borrowedCellShape (entries.flatMap RuntimeEntry.borrowedClassicalCells)).Value :=
  match entries, cells with
  | [], _ => .unit
  | entry :: tail, values =>
      prependBorrowedCell entry (tail.flatMap RuntimeEntry.borrowedClassicalCells) values.1
        (readBorrowedCells (kind := kind) tail values.2)
termination_by structural entries

private theorem readBorrowedCells_write {kind : ProblemKind}
    {key : StorageKey} {role : StorageRole} {shape : CShape}
    {entries : List (RuntimeEntry kind)} (cells : Cells entries)
    (slot : RuntimeEntrySlot (.storage key role shape) entries)
    (value : shape.Value) (writable : role ≠ .borrowedInput) :
    readBorrowedCells entries (Cells.write cells slot value) =
      readBorrowedCells entries cells := by
  induction slot with
  | here =>
      cases role with
      | borrowedInput => exact False.elim (writable rfl)
      | workspace | retained | finalOutput => rfl
  | @there entry entries slot ih =>
      change prependBorrowedCell entry _ cells.1
        (readBorrowedCells entries (Cells.write cells.2 slot value)) =
          prependBorrowedCell entry _ cells.1 (readBorrowedCells entries cells.2)
      rw [ih cells.2]

namespace Store

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The complete borrowed classical value, observed from this actual store. -/
def readBorrowedClassical (store : Store ctx) : ctx.borrowedClassicalShape.Value :=
  readBorrowedCells ctx.entries store.cells

/-- A typed writable cell can never overwrite any part of the borrowed input. -/
theorem readBorrowedClassical_write {shape : CShape} (store : Store ctx)
    (output : CWriteRef ctx shape) (value : shape.Value) :
    (store.write output value).readBorrowedClassical = store.readBorrowedClassical :=
  readBorrowedCells_write store.cells output.slot value output.writable

/-- Every closed classical instruction retains the entire borrowed classical value. -/
theorem readBorrowedClassical_applyOp {input output : CShape} (store : Store ctx)
    (op : ClassicalOp input output ctx ctx) :
    (store.applyOp op).readBorrowedClassical = store.readBorrowedClassical :=
  store.readBorrowedClassical_write op.outputRef _

@[simp] theorem readBorrowedClassical_empty :
    (Store.empty (kind := kind)).readBorrowedClassical = .unit := rfl

/-- Allocating fresh lexical storage preserves all actual borrowed values. -/
theorem readBorrowedClassical_pushWorkspace (store : Store ctx)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (store.pushWorkspace key shape fresh).readBorrowedClassical =
      store.readBorrowedClassical := rfl

/-- Releasing the lexical head preserves the complete remaining borrowed readout. -/
theorem readBorrowedClassical_popWorkspace (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) (store : Store (ctx.addWorkspace key shape fresh)) :
    (Store.popWorkspace key shape fresh store).readBorrowedClassical =
      store.readBorrowedClassical := rfl

/-- Keeping a new result cell changes no actual borrowed value. -/
theorem readBorrowedClassical_pushRetained (store : Store ctx)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (store.pushRetained key shape fresh).readBorrowedClassical =
      store.readBorrowedClassical := rfl

/-- Quantum preparation adds a presence marker and keeps every borrowed classical value. -/
theorem readBorrowedClassical_pushOwnedLayout {ctx : RuntimeCtx .quantum} (store : Store ctx)
    (key : StorageKey) {systemCount : Nat} (layout : QuantumLayout systemCount)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (store.pushOwnedLayout key layout fresh disjoint).readBorrowedClassical =
      store.readBorrowedClassical := rfl

end Store

end Execution

namespace Circuit

/-- The circuit preserves all borrowed classical cell identities and their ordered shapes. -/
theorem borrowedClassicalCells_preserved {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) : post.borrowedClassicalCells = pre.borrowedClassicalCells := by
  induction code with
  | id | classical | classicalQuery | unitary | measureZ | iterate | workspace => rfl
  | retain ctx key shape fresh => exact ctx.borrowedClassicalCells_addRetained key shape fresh
  | prepareZero ctx key layout fresh disjoint =>
      exact ctx.borrowedClassicalCells_addOwnedLayout key layout fresh disjoint
  | seq first second firstIH secondIH => exact secondIH.trans firstIH
  | branch input body bodyIH => exact bodyIH (CShape.initialValue _)

/-- The borrowed classical observation has one common shape before and after execution. -/
theorem borrowedClassicalShape_preserved {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) : post.borrowedClassicalShape = pre.borrowedClassicalShape :=
  RuntimeCtx.borrowedClassicalShape_eq code.borrowedClassicalCells_preserved

/-- Compare the same borrowed classical values across the circuit's exact shape equality. -/
def borrowedClassicalValueTransport {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) :
    post.borrowedClassicalShape.Value ≃ pre.borrowedClassicalShape.Value :=
  Equiv.cast (congrArg CShape.Value code.borrowedClassicalShape_preserved)

end Circuit

end QuantumAlg
