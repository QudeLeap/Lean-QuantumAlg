/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Denominator
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Row

/-!
# Exact preserved reads of the original seven-operation denominator row

The actual shared subtraction overwrites its one scalar temporary and the
following native instruction overwrites its selected C row. Every other
structural read and every unvisited array row keeps its original word.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Every structural read outside the two actual output cells is unchanged. -/
lemma denominatorStore_read_other (seed row : Fin length) (store : Store ctx)
    {shape : CShape} (observed : CInputRef ctx shape)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (denominatorFree : frame.arrays.c.key ∉ observed.storageKeys) :
    (frame.denominatorStore seed row store).read observed = store.read observed := by
  exact (Store.read_applyOp_of_not_mem_storageKeys _
    (rowWriteOp frame.arrays.c row (wordRead frame.work.temporary)) observed denominatorFree).trans
    (Store.read_write_of_not_mem_storageKeys _ _ _ observed temporaryFree)

/-- All other actual array rows are retained even when their physical array is C itself. -/
lemma denominatorStore_read_other_row (seed selected : Fin length) (store : Store ctx)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ selected) :
    (frame.denominatorStore seed selected store).read (rowRead array row) =
      store.read (rowRead array row) := by
  exact (rowWrite_read_of_row_ne _ _ _ _ _ _ different).trans
    (wordWrite_read_row _ _ _ _ _)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- The actual retained subtraction/write record has those exact same protected reads. -/
lemma denominatorRecord_read_other (seed row : Fin length) (environment : model.Environment)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (denominatorFree : frame.arrays.c.key ∉ observed.storageKeys) :
    (frame.denominatorRecord seed row environment store).1.read observed = store.read observed := by
  rw [frame.denominatorRecord_store]
  exact frame.denominatorStore_read_other seed row store observed temporaryFree denominatorFree

/-- Its actual path-bearing record preserves every original unvisited array row as well. -/
lemma denominatorRecord_read_other_row (seed selected : Fin length)
    (environment : model.Environment) (store : Store ctx)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ selected) :
    (frame.denominatorRecord seed selected environment store).1.read (rowRead array row) =
      store.read (rowRead array row) := by
  rw [frame.denominatorRecord_store]
  exact frame.denominatorStore_read_other_row seed selected store array row different

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
