/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Store
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Row

/-!
# Unvisited coordinate rows of actual doubling

Only the supplied destination row is changed in either physical array.
Every other row survives all scalar arithmetic and both destination
overwrites, even when the selected source is doubled in place.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- Every actual array word outside the original destination row remains exactly unchanged. -/
lemma doubleStore_read_other_row (spec : ModulusSpec width) (source destination : Fin length)
    (store : Store ctx) (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ destination) :
    (frame.doubleStore spec source destination store).read (rowRead array row) =
      store.read (rowRead array row) := by
  apply RowInstruction.updates_read_other_row
  intro index
  fin_cases index <;> simp [instructions, RowInstruction.writtenRow, Ne.symm different]

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : CoordinateFrame ctx width length)

/-- The same actual full interpreter record retains every unvisited coordinate row. -/
lemma doubleRecord_read_other_row (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ destination) :
    (frame.doubleRecord spec source destination environment before).1.1.read (rowRead array row) =
      before.1.read (rowRead array row) := by
  rw [frame.doubleRecord_store]
  exact frame.doubleStore_read_other_row spec source destination before.1 array row different

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
