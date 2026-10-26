/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Instructions
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Arithmetic
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Separation

/-!
# Actual negative tangent-denominator row values

The three original slots read the original coordinate, add it to itself,
subtract that canonical result from the real zero input and overwrite C.
The exact returned word and its field value belong to the same actual
record, with no promise about the old scalar working words.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- Actual total Store projection of the original three paid slots. -/
def tangentStore (spec : ModulusSpec width) (row : Fin length) (store : Store ctx) : Store ctx :=
  RowInstruction.updates spec frame.modulus 3 (frame.tangentInstructions row) store

/-- The final real C overwrite contains precisely the finite negative doubled-y word. -/
lemma tangentStore_read_result (spec : ModulusSpec width) (row : Fin length) (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.tangentStore spec row store).read (rowRead frame.arrays.c row) =
      subValue (store.read frame.zero)
        (addValue (store.read (rowRead frame.arrays.y row))
          (store.read (rowRead frame.arrays.y row)) (.unsignedWord spec.extendedWord))
        (.unsignedWord spec.extendedWord) := by
  let first := store.write frame.work.product
    (addValue (store.read (rowRead frame.arrays.y row))
      (store.read (rowRead frame.arrays.y row)) (store.read (wordRead frame.modulus)))
  let second := first.write frame.work.temporary
    (subValue (first.read frame.zero) (first.read (wordRead frame.work.product))
      (first.read (wordRead frame.modulus)))
  change (second.applyOp (rowWriteOp frame.arrays.c row (wordRead frame.work.temporary))).read
    (rowRead frame.arrays.c row) = _
  rw [rowWrite_read_same]
  change (second.read (.storage frame.work.temporary.toCStorageRef)) = _
  rw [Store.read_write_same]
  have zeroFree : frame.work.product.key ∉ frame.zero.storageKeys :=
    frame.protectedReads frame.zero (by simp) frame.work.product.key (by simp)
  have modulusFree : frame.work.product.key ∉ (wordRead frame.modulus).storageKeys := by
    change frame.work.product.key ∉ [frame.modulus.key]
    simpa only [List.mem_singleton] using Ne.symm
      (modulus_word_key_ne frame.modulus frame.work.product)
  have productValue : first.read (wordRead frame.work.product) =
      addValue (store.read (rowRead frame.arrays.y row))
        (store.read (rowRead frame.arrays.y row)) (store.read (wordRead frame.modulus)) :=
    Store.read_write_same _ _ _
  have zeroValue : first.read frame.zero = store.read frame.zero :=
    Store.read_write_of_not_mem_storageKeys _ _ _ _ zeroFree
  have modulusValue : first.read (wordRead frame.modulus) = store.read (wordRead frame.modulus) :=
    Store.read_write_of_not_mem_storageKeys _ _ _ _ modulusFree
  rw [zeroValue, productValue, modulusValue, loaded]

/-- The original paid zero input and actual row give exactly the original -2y denominator. -/
lemma tangentStore_result_cast (spec : ModulusSpec width) (row : Fin length) (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord)
    (zero : (store.read frame.zero).toNat = 0) :
    (((frame.tangentStore spec row store).read (rowRead frame.arrays.c row)).toNat :
      ZMod spec.modulus) = -((2 : ZMod spec.modulus) *
        (store.read (rowRead frame.arrays.y row)).toNat) := by
  rw [frame.tangentStore_read_result spec row store loaded,
    subValue_cast spec _ _ (addValue_canonical spec _ _), addValue_cast, zero, Nat.cast_zero]
  ring

/-- That same real C word is canonical for the original loaded modulus. -/
lemma tangentStore_result_canonical (spec : ModulusSpec width) (row : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    ((frame.tangentStore spec row store).read (rowRead frame.arrays.c row)).toNat <
      spec.modulus := by
  rw [frame.tangentStore_read_result spec row store loaded]
  exact subValue_canonical spec _ _ (addValue_canonical spec _ _)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  (frame : TableFrame ctx width length)

/-- The real three-slot row record keeps each predecessor's actual Store and service state. -/
def tangentRecord (spec : ModulusSpec width) (row : Fin length) (environment : model.Environment) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (frame.tangentDenominatorRow (model := model) row).Path :=
  RowInstruction.rangeRecord spec frame.modulus environment 3 (frame.tangentInstructions row)

/-- The proved total word Store is precisely the actual returned Store, including old aliases. -/
lemma tangentRecord_store (spec : ModulusSpec width) (row : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.tangentRecord spec row environment before).1.1 =
      frame.tangentStore spec row before.1 :=
  RowInstruction.rangeRecord_store spec frame.modulus environment 3
    (frame.tangentInstructions row) before

/-- The same denominator record retains every incoming history and arbitrary Reference block. -/
lemma tangentDenominatorRow_execute (spec : ModulusSpec width) (row : Fin length)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.tangentDenominatorRow (model := model) row).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.tangentRecord spec row environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  RowInstruction.range_execute spec frame.modulus environment 3 (frame.tangentInstructions row)
    Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
