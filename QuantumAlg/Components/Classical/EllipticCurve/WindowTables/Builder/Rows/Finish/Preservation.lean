/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Row

/-!
# Every other row survives the original final five-column conversion

The actual fifteen slots overwrite only the selected row in the five
physical arrays. All unvisited coordinate/inverse rows and already
finished rows remain unchanged through the same actual record.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Every other array row survives all fifteen original finite-word updates exactly. -/
lemma finishStore_read_other_row (spec : ModulusSpec width) (selected : Fin length)
    (store : Store ctx) (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ selected) :
    (frame.finishStore spec selected store).read (rowRead array row) =
      store.read (rowRead array row) := by
  apply RowInstruction.updates_read_other_row
  intro index
  fin_cases index <;> simp [finishInstructions, RowInstruction.writtenRow, Ne.symm different]

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- The full chronological interpreter record preserves that same complete unvisited word. -/
lemma finishRecord_read_other_row (spec : ModulusSpec width) (selected : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ selected) :
    (frame.finishRecord spec selected environment before).1.1.read (rowRead array row) =
      before.1.read (rowRead array row) := by
  rw [frame.finishRecord_store]
  exact frame.finishStore_read_other_row spec selected before.1 array row different

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
