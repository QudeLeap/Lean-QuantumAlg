/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Relabeling.References

/-!
# The complete finite store under injective placement

Every cell retains its exact finite value in the same computational position.
The store correspondence is invertible even when the physical and key maps are
only injective: its target consists precisely of the mapped original entries.
Actual structural reads and writable-cell updates commute with this map.
-/

namespace QuantumAlg.Execution.ContextRelabeling

variable {kind : ProblemKind}
  (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)

private def cellEquiv (entry : RuntimeEntry kind) :
    CellValue entry ≃ CellValue (entry.relabel keys physical) := by
  cases entry <;> exact Equiv.refl _

private def cellsEquiv : (entries : List (RuntimeEntry kind)) →
    Cells entries ≃ Cells (entries.map (RuntimeEntry.relabel keys physical))
  | [] => Equiv.refl _
  | head :: tail => (cellEquiv keys physical head).prodCongr (cellsEquiv tail)

private theorem cells_read {entry : RuntimeEntry kind} {entries : List (RuntimeEntry kind)}
    (cells : Cells entries) (ref : RuntimeEntrySlot entry entries) :
    Cells.read (cellsEquiv keys physical entries cells) (slot keys physical ref) =
      cellEquiv keys physical entry (Cells.read cells ref) := by
  induction ref with
  | here => rfl
  | there next ih => exact ih cells.2

private theorem cells_write {entry : RuntimeEntry kind} {entries : List (RuntimeEntry kind)}
    (cells : Cells entries) (ref : RuntimeEntrySlot entry entries) (value : CellValue entry) :
    cellsEquiv keys physical entries (Cells.write cells ref value) =
      Cells.write (cellsEquiv keys physical entries cells) (slot keys physical ref)
        (cellEquiv keys physical entry value) := by
  induction ref with
  | here => rfl
  | there next ih =>
      exact congrArg (fun tail => (cellEquiv keys physical _ cells.1, tail)) (ih cells.2)

/-- Relabel the complete finite store, preserving every value and quantum presence marker. -/
def storeEquiv (ctx : RuntimeCtx kind) : Store ctx ≃ Store (ctx.relabel keys physical) where
  toFun original := ⟨cellsEquiv keys physical ctx.entries original.cells⟩
  invFun placed := ⟨(cellsEquiv keys physical ctx.entries).symm placed.cells⟩
  left_inv original := by
    cases original
    exact congrArg Store.mk ((cellsEquiv keys physical ctx.entries).symm_apply_apply _)
  right_inv placed := by
    cases placed
    exact congrArg Store.mk ((cellsEquiv keys physical ctx.entries).apply_symm_apply _)

/-- A storage read obtains the identical finite value at the mapped actual cell. -/
theorem store_read_storage {ctx : RuntimeCtx kind} (original : Store ctx) {shape : CShape}
    (ref : CStorageRef ctx shape) :
    (storeEquiv keys physical ctx original).read (.storage (storage keys physical ref)) =
      original.read (.storage ref) :=
  cells_read keys physical original.cells ref.slot

/-- Every compound read keeps its actual finite value, including bit and word projections. -/
theorem store_read_input {ctx : RuntimeCtx kind} (original : Store ctx) {shape : CShape}
    (ref : CInputRef ctx shape) :
    (storeEquiv keys physical ctx original).read (input keys physical ref) =
      original.read ref := by
  induction ref with
  | storage ref => exact store_read_storage keys physical original ref
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector refs ih => exact congrArg CShape.Value.fixedVector (funext ih)
  | first ref ih => exact congrArg CShape.Value.first ih
  | second ref ih => exact congrArg CShape.Value.second ih
  | vectorGet ref index ih => exact congrArg (fun value => value.get index) ih
  | bitsGet ref index ih => exact congrArg (fun value => value.bitGet index) ih
  | wordBitGet ref index ih => exact congrArg (fun value => value.wordBitGet index) ih

/-- The identical writable-cell update commutes with complete finite-store placement. -/
theorem store_write {ctx : RuntimeCtx kind} (original : Store ctx) {shape : CShape}
    (output : CWriteRef ctx shape) (value : CShape.Value shape) :
    storeEquiv keys physical ctx (original.write output value) =
      (storeEquiv keys physical ctx original).write (writable keys physical output) value :=
  congrArg Store.mk (cells_write keys physical original.cells output.toCStorageRef.slot value)

end QuantumAlg.Execution.ContextRelabeling
