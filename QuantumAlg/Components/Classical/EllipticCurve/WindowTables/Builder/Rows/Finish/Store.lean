/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Instructions
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Read
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Protection
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Values
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Finish.Observation

/-!
# Actual Store of the final five-column conversion

The original fifteen paid slots overwrite exactly the original reused
columns. Their finite-word results read the original coordinate row,
already-inverted C row and supplied constant inputs. The actual record
retains every original history and arbitrary quantum-reference block.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- The literal physical destination order of the final five-column interface. -/
def finishColumns : Fin 5 → CWriteRef ctx (.fixedVector length (.unsignedWord width)) :=
  ![frame.arrays.x, frame.arrays.y, frame.arrays.c, frame.arrays.d, frame.arrays.e]

/-- Total finite-word Store of the original final fifteen slots. -/
def finishStore (spec : ModulusSpec width) (row : Fin length) (store : Store ctx) : Store ctx :=
  RowInstruction.updates spec frame.modulus 15 (frame.finishInstructions row) store

/-- Every real final column receives its exact original-input finite-word expression. -/
lemma finishStore_read_values (spec : ModulusSpec width) (row : Fin length) (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord)
    (index : Fin 5) :
    (frame.finishStore spec row store).read (rowRead (frame.finishColumns index) row) =
      finishWords spec (store.read (rowRead frame.arrays.x row))
        (store.read (rowRead frame.arrays.y row)) (store.read frame.curveA)
        (store.read (rowRead frame.arrays.c row)) (store.read frame.zero)
        (store.read frame.one) index := by
  let first := frame.finishFirstStore spec row store
  let middle := frame.finishMiddleStore spec row first
  have firstInputs : FinishInputReads frame row store first :=
    frame.finishFirstStore_inputReads spec row store
  have middleInputs : FinishInputReads frame row first middle :=
    frame.finishMiddleStore_inputReads spec row first
  have originalInputs := FinishInputReads.trans frame row store first middle
    firstInputs middleInputs
  have firstLoaded := firstInputs.modulus.trans loaded
  have middleLoaded := originalInputs.modulus.trans loaded
  rw [finishStore, frame.finish_updates_eq_blocks spec row store]
  fin_cases index
  · change (frame.finishLastStore spec row middle).read (rowRead frame.arrays.x row) =
      Field.Native.Shared.subValue (store.read frame.zero)
        (store.read (rowRead frame.arrays.x row)) (.unsignedWord spec.extendedWord)
    rw [frame.finishLastStore_read_x spec row middle middleLoaded,
      originalInputs.zero, originalInputs.x]
  · change (frame.finishLastStore spec row middle).read (rowRead frame.arrays.y row) =
      Field.Native.Shared.subValue (store.read frame.zero)
        (store.read (rowRead frame.arrays.y row)) (.unsignedWord spec.extendedWord)
    rw [frame.finishLastStore_read_y spec row middle middleLoaded,
      originalInputs.zero, originalInputs.y]
  · change (frame.finishLastStore spec row middle).read (rowRead frame.arrays.c row) =
      Field.Native.Shared.addValue
        (Field.Native.Shared.addValue (store.read (rowRead frame.arrays.x row))
          (store.read (rowRead frame.arrays.x row)) (.unsignedWord spec.extendedWord))
        (store.read (rowRead frame.arrays.x row)) (.unsignedWord spec.extendedWord)
    rw [frame.finishLastStore_read_other spec row middle (rowRead frame.arrays.c row)
      (array_row_free _ _ _ (frame.arrays.column_key_ne 4 2 (by decide)))
      (array_row_free _ _ _ (frame.arrays.column_key_ne 0 2 (by decide)))
      (array_row_free _ _ _ (frame.arrays.column_key_ne 1 2 (by decide)))
      (scalar_row_free _ _ _), frame.finishMiddleStore_read_c spec row first firstLoaded,
      firstInputs.x]
  · change (frame.finishLastStore spec row middle).read (rowRead frame.arrays.d row) =
      multiplyValue (finishNumeratorWord spec (store.read (rowRead frame.arrays.x row))
        (store.read frame.curveA)) (store.read (rowRead frame.arrays.c row))
        (.unsignedWord spec.extendedWord)
    rw [frame.finishLastStore_read_other spec row middle (rowRead frame.arrays.d row)
      (array_row_free _ _ _ (frame.arrays.column_key_ne 4 3 (by decide)))
      (array_row_free _ _ _ (frame.arrays.column_key_ne 0 3 (by decide)))
      (array_row_free _ _ _ (frame.arrays.column_key_ne 1 3 (by decide)))
      (scalar_row_free _ _ _), frame.finishMiddleStore_read_d spec row first,
      frame.finishFirstStore_read_slope spec row store loaded]
  · change (frame.finishLastStore spec row middle).read (rowRead frame.arrays.e row) =
      Field.Native.Shared.addValue (store.read (rowRead frame.arrays.x row))
        (store.read frame.one) (.unsignedWord spec.extendedWord)
    rw [frame.finishLastStore_read_e spec row middle,
      frame.finishMiddleStore_read_temporary spec row first firstLoaded,
      firstInputs.x, firstInputs.one]

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- Actual complete record of the unchanged final fifteen paid slots. -/
def finishRecord (spec : ModulusSpec width) (row : Fin length) (environment : model.Environment) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (frame.finishRow (model := model) row).Path :=
  RowInstruction.rangeRecord spec frame.modulus environment 15 (frame.finishInstructions row)

/-- Its exact Store is the same total finite-word Store used for the column-value proof. -/
lemma finishRecord_store (spec : ModulusSpec width) (row : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.finishRecord spec row environment before).1.1 = frame.finishStore spec row before.1 :=
  RowInstruction.rangeRecord_store spec frame.modulus environment 15
    (frame.finishInstructions row) before

/-- Every incoming matrix block and chronological history uses that same real overwrite record. -/
lemma finishRow_execute (spec : ModulusSpec width) (row : Fin length)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.finishRow (model := model) row).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.finishRecord spec row environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  RowInstruction.range_execute spec frame.modulus environment 15 (frame.finishInstructions row)
    Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
