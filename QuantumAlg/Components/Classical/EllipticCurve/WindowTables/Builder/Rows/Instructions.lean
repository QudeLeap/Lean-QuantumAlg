/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Sequence

/-!
# The original table rows as literal native instruction slots

Each family below is definitionally the original row program. This names
its chronological Store updates for value proofs without changing code,
operand placement, native labels, arithmetic scopes or instruction costs.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

local notation "p" => wordRead frame.work.product
local notation "i" => wordRead frame.work.inverse
local notation "t" => wordRead frame.work.temporary
local notation "s" => wordRead frame.work.slope

/-- The original fifteen paid slots of the shared-modulus doubling row. -/
def doubleInstructions (source destination : Fin length) :
    Fin 15 → RowInstruction ctx width length :=
  let x := rowRead frame.arrays.x source
  let y := rowRead frame.arrays.y source
  ![.add y y frame.work.product,
    .coefficient p frame.work.inverse,
    .multiply x x frame.work.temporary,
    .add t t frame.work.product,
    .add p t frame.work.product,
    .add p frame.curveA frame.work.product,
    .multiply p i frame.work.slope,
    .add x x frame.work.product,
    .multiply s s frame.work.temporary,
    .sub t p frame.work.product,
    .sub x p frame.work.temporary,
    .multiply s t frame.work.temporary,
    .sub t y frame.work.temporary,
    .write frame.arrays.x destination p,
    .write frame.arrays.y destination t]

/-- The original ten paid slots of a nonexceptional extension row. -/
def extendInstructions (seed row destination : Fin length) :
    Fin 10 → RowInstruction ctx width length :=
  let x := rowRead frame.arrays.x row
  let y := rowRead frame.arrays.y row
  let bx := rowRead frame.arrays.x seed
  let baseY := rowRead frame.arrays.y seed
  ![.sub baseY y frame.work.temporary,
    .multiply t (rowRead frame.arrays.c row) frame.work.slope,
    .multiply s s frame.work.temporary,
    .sub t x frame.work.temporary,
    .sub t bx frame.work.temporary,
    .sub x t frame.work.product,
    .multiply s p frame.work.product,
    .sub p y frame.work.product,
    .write frame.arrays.x destination t,
    .write frame.arrays.y destination p]

/-- The original three paid slots computing the literal negative tangent denominator. -/
def tangentInstructions (row : Fin length) : Fin 3 → RowInstruction ctx width length :=
  let y := rowRead frame.arrays.y row
  ![.add y y frame.work.product,
    .sub frame.zero p frame.work.temporary,
    .write frame.arrays.c row t]

/-- The original fifteen paid slots of the final five-column overwrite. -/
def finishInstructions (row : Fin length) : Fin 15 → RowInstruction ctx width length :=
  let x := rowRead frame.arrays.x row
  let y := rowRead frame.arrays.y row
  ![.multiply x x frame.work.temporary,
    .add t t frame.work.product,
    .add p t frame.work.product,
    .add p frame.curveA frame.work.product,
    .multiply p (rowRead frame.arrays.c row) frame.work.slope,
    .write frame.arrays.d row s,
    .add x x frame.work.temporary,
    .add t x frame.work.temporary,
    .write frame.arrays.c row t,
    .add x frame.one frame.work.temporary,
    .write frame.arrays.e row t,
    .sub frame.zero x frame.work.temporary,
    .write frame.arrays.x row t,
    .sub frame.zero y frame.work.temporary,
    .write frame.arrays.y row t]

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- Naming the doubling slots leaves the original actual circuit unchanged. -/
lemma doubleRow_eq_instructions (spec : ModulusSpec width) (source destination : Fin length) :
    frame.doubleRow (model := model) spec source destination = Circuit.forRange 15
      (fun index => (frame.doubleInstructions source destination index).circuit spec
        frame.modulus) := rfl

/-- Naming the extension slots leaves the original actual circuit unchanged. -/
lemma extendRow_eq_instructions (spec : ModulusSpec width) (seed row destination : Fin length) :
    frame.extendRow (model := model) seed row destination = Circuit.forRange 10
      (fun index => (frame.extendInstructions seed row destination index).circuit spec
        frame.modulus) := rfl

/-- Naming the tangent slots leaves the original actual circuit unchanged. -/
lemma tangentDenominatorRow_eq_instructions (spec : ModulusSpec width) (row : Fin length) :
    frame.tangentDenominatorRow (model := model) row = Circuit.forRange 3
      (fun index => (frame.tangentInstructions row index).circuit spec frame.modulus) := rfl

/-- Naming the final overwrite slots leaves the original actual circuit unchanged. -/
lemma finishRow_eq_instructions (spec : ModulusSpec width) (row : Fin length) :
    frame.finishRow (model := model) row = Circuit.forRange 15
      (fun index => (frame.finishInstructions row index).circuit spec frame.modulus) := rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
