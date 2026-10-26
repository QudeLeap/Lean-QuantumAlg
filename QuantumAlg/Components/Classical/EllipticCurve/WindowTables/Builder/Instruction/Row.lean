/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Framing
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows.Read
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.ReadWrite

/-!
# Exact preservation of unvisited rows by the original paid slots

Scalar writes retain every array row by the actual stored shapes. An
array overwrite retains a different row whether its physical array is
the observed array or a different one. These facts follow the real total
Store updates, with no assumptions on old scalar or destination values.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

private lemma writeRef_eq_of_key {shape : CShape} (first second : CWriteRef ctx shape)
    (same : first.key = second.key) : first = second := by
  have underlying := CStorageRef.storageRef_eq_of_key first.toCStorageRef second.toCStorageRef same
  cases first
  cases second
  cases underlying
  rfl

/-- A different row survives the actual overwrite, including when both arrays are identical. -/
lemma rowWrite_read_of_row_ne
    (written observed : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index selected : Fin length) (input : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) (different : selected ≠ index) :
    (store.applyOp (rowWriteOp written index input)).read (rowRead observed selected) =
      store.read (rowRead observed selected) := by
  by_cases same : written.key = observed.key
  · have equal := writeRef_eq_of_key written observed same
    subst observed
    exact rowWrite_read_other written index input store selected different
  · exact rowWrite_read_array written observed index selected input store same

namespace RowInstruction

/-- The actual array row overwritten by the original slot, when it has an array output. -/
def writtenRow (instruction : RowInstruction ctx width length) : Option (Fin length) :=
  match instruction with
  | .write _ row _ => some row
  | _ => none

/-- A scalar slot or an actual array write at another index retains the selected entire word. -/
lemma update_read_other_row (instruction : RowInstruction ctx width length)
    (spec : ModulusSpec width) (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (store : Store ctx) (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : instruction.writtenRow ≠ some row) :
    (instruction.update spec modulus store).read (rowRead array row) =
      store.read (rowRead array row) := by
  cases instruction with
  | add left right output => exact wordWrite_read_row _ _ _ _ _
  | sub left right output => exact wordWrite_read_row _ _ _ _ _
  | multiply left right output => exact wordWrite_read_row _ _ _ _ _
  | coefficient input output => exact wordWrite_read_row _ _ _ _ _
  | write written index input =>
      apply rowWrite_read_of_row_ne
      intro same
      apply different
      change some index = some row
      rw [same]

/-- Every selected original slot preserves an unvisited row on its true intermediate Store. -/
lemma updates_read_other_row (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (count : Nat)
    (instructions : Fin count → RowInstruction ctx width length) (store : Store ctx)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) (row : Fin length)
    (different : ∀ index, (instructions index).writtenRow ≠ some row) :
    (updates spec modulus count instructions store).read (rowRead array row) =
      store.read (rowRead array row) := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      exact (ih (fun index => instructions index.succ)
        ((instructions 0).update spec modulus store) (fun index => different index.succ)).trans
          ((instructions 0).update_read_other_row spec modulus store array row (different 0))

end RowInstruction

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
