/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Tangent
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Row

/-!
# Complete protected reads of the original negative-tangent preparation

Only product, temporary and the selected C row change. Every structural
read outside those real output cells, and every other actual array row,
retains its exact original finite word through the same physical record.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Every structural read outside the three actual tangent-preparation outputs survives. -/
lemma tangentStore_read_other (spec : ModulusSpec width) (row : Fin length) (store : Store ctx)
    {shape : CShape} (observed : CInputRef ctx shape)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (denominatorFree : frame.arrays.c.key ∉ observed.storageKeys) :
    (frame.tangentStore spec row store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;> first | exact productFree | exact temporaryFree | exact denominatorFree

/-- Every other original array row survives the three actual tangent-preparation slots. -/
lemma tangentStore_read_other_row (spec : ModulusSpec width) (selected : Fin length)
    (store : Store ctx) (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ selected) :
    (frame.tangentStore spec selected store).read (rowRead array row) =
      store.read (rowRead array row) := by
  apply RowInstruction.updates_read_other_row
  intro index
  fin_cases index <;> simp [tangentInstructions, RowInstruction.writtenRow, Ne.symm different]

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- The complete actual retained record has those same structural read values. -/
lemma tangentRecord_read_other (spec : ModulusSpec width) (row : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (denominatorFree : frame.arrays.c.key ∉ observed.storageKeys) :
    (frame.tangentRecord spec row environment before).1.1.read observed =
      before.1.read observed := by
  rw [frame.tangentRecord_store]
  exact frame.tangentStore_read_other spec row before.1 observed productFree temporaryFree
    denominatorFree

/-- The original full chronological record also preserves every unvisited actual array row. -/
lemma tangentRecord_read_other_row (spec : ModulusSpec width) (selected : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ selected) :
    (frame.tangentRecord spec selected environment before).1.1.read (rowRead array row) =
      before.1.read (rowRead array row) := by
  rw [frame.tangentRecord_store]
  exact frame.tangentStore_read_other_row spec selected before.1 array row different

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
