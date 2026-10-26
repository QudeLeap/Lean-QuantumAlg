/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Extend.First

/-!
# Exact new-x word of the original secant row

The three real slots square the prepared slope and perform the original
two subtractions. Both coordinate arrays and the loaded modulus retain
their preceding values through every temporary-word overwrite.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular Field.Native.Shared

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}
  (frame : TableFrame ctx width length)

/-- The actual temporary word contains precisely the original finite-word secant new x. -/
lemma extendXStore_read_temporary (spec : ModulusSpec width) (seed row : Fin length)
    (store : Store ctx)
    (loaded : store.read (wordRead frame.modulus) = .unsignedWord spec.extendedWord) :
    (frame.extendXStore spec seed row store).read (wordRead frame.work.temporary) =
      subValue (subValue (multiplyValue (store.read (wordRead frame.work.slope))
        (store.read (wordRead frame.work.slope)) (.unsignedWord spec.extendedWord))
        (store.read (rowRead frame.arrays.x row)) (.unsignedWord spec.extendedWord))
        (store.read (rowRead frame.arrays.x seed)) (.unsignedWord spec.extendedWord) := by
  let first := store.write frame.work.temporary
    (multiplyValue (store.read (wordRead frame.work.slope))
      (store.read (wordRead frame.work.slope)) (store.read (wordRead frame.modulus)))
  let second := first.write frame.work.temporary
    (subValue (first.read (wordRead frame.work.temporary))
      (first.read (rowRead frame.arrays.x row)) (first.read (wordRead frame.modulus)))
  have firstTemporary : first.read (wordRead frame.work.temporary) =
      multiplyValue (store.read (wordRead frame.work.slope))
        (store.read (wordRead frame.work.slope)) (store.read (wordRead frame.modulus)) :=
    Store.read_write_same _ _ _
  have firstX : first.read (rowRead frame.arrays.x row) =
      store.read (rowRead frame.arrays.x row) := wordWrite_read_row _ _ _ store _
  have firstModulus : first.read (wordRead frame.modulus) =
      store.read (wordRead frame.modulus) := wordWrite_read_modulus _ _ store _
  have secondTemporary : second.read (wordRead frame.work.temporary) =
      subValue (first.read (wordRead frame.work.temporary))
        (first.read (rowRead frame.arrays.x row)) (first.read (wordRead frame.modulus)) :=
    Store.read_write_same _ _ _
  have secondBaseX : second.read (rowRead frame.arrays.x seed) =
      store.read (rowRead frame.arrays.x seed) :=
    (wordWrite_read_row _ _ _ first _).trans (wordWrite_read_row _ _ _ store _)
  have secondModulus : second.read (wordRead frame.modulus) =
      store.read (wordRead frame.modulus) :=
    (wordWrite_read_modulus _ _ first _).trans firstModulus
  change (second.write frame.work.temporary
    (subValue (second.read (wordRead frame.work.temporary))
      (second.read (rowRead frame.arrays.x seed))
      (second.read (wordRead frame.modulus)))).read (wordRead frame.work.temporary) = _
  rw [wordWrite_read_same, secondTemporary, secondBaseX, secondModulus,
    firstTemporary, firstX, firstModulus, loaded]

/-- The three original new-x slots overwrite only the existing temporary word. -/
lemma extendXStore_read_other (spec : ModulusSpec width) (seed row : Fin length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys) :
    (frame.extendXStore spec seed row store).read observed = store.read observed := by
  apply RowInstruction.updates_read_other
  intro index
  fin_cases index <;> exact temporaryFree

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
