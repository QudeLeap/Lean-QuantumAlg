/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates

/-!
# Actual preparation of the two small window-base coordinate arrays

The real input coordinates are copied once into row zero. Each next row
is obtained by sixteen original paid doublings, with the final fifteen
performed in place. The supplied two arrays and four scalar words are
reused throughout; no three extra small arrays are introduced.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- Two actual native copies initialize one original coordinate row. -/
def seedCircuit (sourceX sourceY : CInputRef ctx (.unsignedWord width)) (row : Fin length) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (rowWriteOp frame.x row sourceX))
    (BitWord.instruction (execution := model) (rowWriteOp frame.y row sourceY))

/-- Sixteen actual doublings prepare the next window base, reusing its destination in place. -/
def baseStep (spec : ModulusSpec width) (source destination : Fin length) :
    Circuit model ctx ctx :=
  .seq (frame.doubleCircuit spec source destination)
    (Circuit.forRange 15 (fun _ => frame.doubleCircuit spec destination destination))

variable {baseCount : Nat} (frame : CoordinateFrame ctx width (baseCount + 1))

/-- Existing row zero and every successive window base are constructed by their real paid code. -/
def prepareBases (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (frame.seedCircuit sourceX sourceY ⟨0, Nat.zero_lt_succ _⟩)
    (Circuit.forRange baseCount (fun index => frame.baseStep spec index.castSucc index.succ))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
