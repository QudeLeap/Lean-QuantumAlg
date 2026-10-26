/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Row

/-!
# Exact preserved rows and caller reads of the actual secant record

The original ten slots change only product, temporary, slope and the two
selected destination rows. Every other row, the original inverse array
and protected supplied inputs retain their full original finite values.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Every actual array row outside the selected secant destination remains exactly unchanged. -/
lemma extendStore_read_other_row (spec : ModulusSpec width) (seed source destination : Fin length)
    (store : Store ctx) (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ destination) :
    (frame.extendStore spec seed source destination store).read (rowRead array row) =
      store.read (rowRead array row) := by
  apply RowInstruction.updates_read_other_row
  intro index
  fin_cases index <;> simp [extendInstructions, RowInstruction.writtenRow, Ne.symm different]

/-- Full structural reads outside the five actual secant output cells survive every paid slot. -/
lemma extendStore_read_other (spec : ModulusSpec width) (seed row destination : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (slopeFree : frame.work.slope.key ∉ observed.storageKeys)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (xFree : frame.arrays.x.key ∉ observed.storageKeys)
    (yFree : frame.arrays.y.key ∉ observed.storageKeys) :
    (frame.extendStore spec seed row destination store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;>
    first | exact temporaryFree | exact slopeFree | exact productFree | exact xFree | exact yFree

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- The complete chronological secant interpreter record retains every same unvisited row. -/
lemma extendRecord_read_other_row (spec : ModulusSpec width) (seed source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ destination) :
    (frame.extendRecord spec seed source destination environment before).1.1.read
      (rowRead array row) =
      before.1.read (rowRead array row) := by
  rw [frame.extendRecord_store]
  exact frame.extendStore_read_other_row spec seed source destination before.1 array row different

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
