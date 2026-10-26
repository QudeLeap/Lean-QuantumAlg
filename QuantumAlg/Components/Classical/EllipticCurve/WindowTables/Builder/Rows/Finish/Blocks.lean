/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Instructions
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Blocks

/-!
# Three consecutive blocks of the unchanged final row

The original fifteen slots are grouped into five scalar operations, five
prefix overwrites and five terminal overwrites. The finite-word Store
composition follows exactly that order on its real intermediate values.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

local notation "p" => wordRead frame.work.product
local notation "t" => wordRead frame.work.temporary
local notation "s" => wordRead frame.work.slope

/-- The first five original scalar slots prepare the slope at the negative original point. -/
def finishFirstInstructions (row : Fin length) : Fin 5 → RowInstruction ctx width length :=
  let x := rowRead frame.arrays.x row
  ![.multiply x x frame.work.temporary,
    .add t t frame.work.product,
    .add p t frame.work.product,
    .add p frame.curveA frame.work.product,
    .multiply p (rowRead frame.arrays.c row) frame.work.slope]

/-- The next five original slots write D/C and prepare the original x+1 value. -/
def finishMiddleInstructions (row : Fin length) : Fin 5 → RowInstruction ctx width length :=
  let x := rowRead frame.arrays.x row
  ![.write frame.arrays.d row s,
    .add x x frame.work.temporary,
    .add t x frame.work.temporary,
    .write frame.arrays.c row t,
    .add x frame.one frame.work.temporary]

/-- The last five original slots write E and the two negative coordinate columns. -/
def finishLastInstructions (row : Fin length) : Fin 5 → RowInstruction ctx width length :=
  let x := rowRead frame.arrays.x row
  let y := rowRead frame.arrays.y row
  ![.write frame.arrays.e row t,
    .sub frame.zero x frame.work.temporary,
    .write frame.arrays.x row t,
    .sub frame.zero y frame.work.temporary,
    .write frame.arrays.y row t]

/-- Actual first-block finite-word Store. -/
def finishFirstStore (spec : ModulusSpec width) (row : Fin length) (store : Store ctx) :
    Store ctx :=
  RowInstruction.updates spec frame.modulus 5 (frame.finishFirstInstructions row) store

/-- Actual middle-block finite-word Store. -/
def finishMiddleStore (spec : ModulusSpec width) (row : Fin length) (store : Store ctx) :
    Store ctx :=
  RowInstruction.updates spec frame.modulus 5 (frame.finishMiddleInstructions row) store

/-- Actual last-block finite-word Store. -/
def finishLastStore (spec : ModulusSpec width) (row : Fin length) (store : Store ctx) : Store ctx :=
  RowInstruction.updates spec frame.modulus 5 (frame.finishLastInstructions row) store

/-- Only grouping changes: every original slot and actual intermediate Store is identical. -/
lemma finish_updates_eq_blocks (spec : ModulusSpec width) (row : Fin length) (store : Store ctx) :
    RowInstruction.updates spec frame.modulus 15 (frame.finishInstructions row) store =
      frame.finishLastStore spec row (frame.finishMiddleStore spec row
        (frame.finishFirstStore spec row store)) := by
  have slots : List.ofFn (frame.finishInstructions row) =
      List.ofFn (frame.finishFirstInstructions row) ++
        (List.ofFn (frame.finishMiddleInstructions row) ++
          List.ofFn (frame.finishLastInstructions row)) := rfl
  unfold finishFirstStore finishMiddleStore finishLastStore
  simp only [RowInstruction.updates_eq_foldl]
  rw [slots, List.foldl_append, List.foldl_append]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
