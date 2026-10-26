/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Instructions

/-!
# Literal equality of the existing builder doubling and two-array doubling

The supplied coordinate frame projects the same actual x/y arrays, four
scalar words, widened modulus and curve input. Every original native slot
is identical. This permits both small base arrays and the large builder to
consume the same doubling program without allocating three unused arrays.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Projection to the coordinate-only frame preserves all fifteen original native operands. -/
lemma coordinates_instructions (frame : TableFrame ctx width length)
    (source destination : Fin length) :
    frame.coordinates.instructions source destination = frame.doubleInstructions source
      destination := rfl

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual builder doubling is exactly the existing-storage two-array doubling circuit. -/
lemma doubleRow_eq_coordinateCircuit (frame : TableFrame ctx width length)
    (spec : ModulusSpec width) (source destination : Fin length) :
    frame.doubleRow (model := model) spec source destination =
      frame.coordinates.doubleCircuit spec source destination := by
  rw [frame.doubleRow_eq_instructions]
  apply congrArg (Circuit.forRange 15)
  funext index
  change (frame.doubleInstructions source destination index).circuit spec frame.modulus =
    (frame.coordinates.instructions source destination index).circuit spec frame.modulus
  rw [frame.coordinates_instructions]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
