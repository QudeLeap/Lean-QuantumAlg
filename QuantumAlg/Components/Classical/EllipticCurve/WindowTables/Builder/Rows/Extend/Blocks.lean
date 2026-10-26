/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Instructions
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Result
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Swap

/-!
# Consecutive blocks of the original ten-slot secant row

Two original slots prepare the slope from the actual batch-inverse C word.
Three slots compute the new x. The same three-slot coordinate suffix and
two physical writes already used for doubling finish this row with the
original product/temporary names exchanged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

local notation "t" => wordRead frame.work.temporary
local notation "s" => wordRead frame.work.slope

/-- The two actual secant-prefix slots consume the original batch-inverse row. -/
def extendFirstInstructions (seed row : Fin length) : Fin 2 → RowInstruction ctx width length :=
  ![.sub (rowRead frame.arrays.y seed) (rowRead frame.arrays.y row) frame.work.temporary,
    .multiply t (rowRead frame.arrays.c row) frame.work.slope]

/-- The three actual new-x slots perform the original two coordinate subtractions. -/
def extendXInstructions (seed row : Fin length) : Fin 3 → RowInstruction ctx width length :=
  ![.multiply s s frame.work.temporary,
    .sub t (rowRead frame.arrays.x row) frame.work.temporary,
    .sub t (rowRead frame.arrays.x seed) frame.work.temporary]

/-- Exact total Store of the two original slope slots. -/
def extendFirstStore (spec : ModulusSpec width) (seed row : Fin length) (store : Store ctx) :
    Store ctx :=
  RowInstruction.updates spec frame.modulus 2 (frame.extendFirstInstructions seed row) store

/-- Exact total Store of the three original new-x slots. -/
def extendXStore (spec : ModulusSpec width) (seed row : Fin length) (store : Store ctx) :
    Store ctx :=
  RowInstruction.updates spec frame.modulus 3 (frame.extendXInstructions seed row) store

/-- Exact total Store of all ten unchanged paid secant slots. -/
def extendStore (spec : ModulusSpec width) (seed row destination : Fin length)
    (store : Store ctx) : Store ctx :=
  RowInstruction.updates spec frame.modulus 10 (frame.extendInstructions seed row destination) store

/-- Only grouping and scalar names change; the original ten actual slots are identical. -/
lemma extendStore_eq_blocks (spec : ModulusSpec width) (seed row destination : Fin length)
    (store : Store ctx) :
    frame.extendStore spec seed row destination store =
      frame.coordinates.swapProductTemporary.writeStore spec destination
        (frame.coordinates.swapProductTemporary.resultLastStore spec row
          (frame.extendXStore spec seed row (frame.extendFirstStore spec seed row store))) := by
  have slots : List.ofFn (frame.extendInstructions seed row destination) =
      List.ofFn (frame.extendFirstInstructions seed row) ++
        (List.ofFn (frame.extendXInstructions seed row) ++
          (List.ofFn (frame.coordinates.swapProductTemporary.resultLastInstructions row) ++
            List.ofFn (frame.coordinates.swapProductTemporary.writeInstructions destination))) :=
    rfl
  unfold extendStore extendFirstStore extendXStore CoordinateFrame.resultLastStore
    CoordinateFrame.writeStore
  simp only [RowInstruction.updates_eq_foldl]
  rw [slots, List.foldl_append, List.foldl_append, List.foldl_append]
  rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
