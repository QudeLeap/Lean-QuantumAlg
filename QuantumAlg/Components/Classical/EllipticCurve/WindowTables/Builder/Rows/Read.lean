/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Separation
import all QuantumAlg.Components.Classical.Modular.NativePower.Multiply

/-!
# Structural reads used by actual table-row arithmetic

Typed scalar and array shapes establish their physical key separation.
These exact read laws retain the original array contents, stored modulus
and protected source words through the original scalar overwrites.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution Modular.NativePower

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- A complete table array cannot share a physical cell with the widened scalar modulus. -/
lemma modulus_array_key_ne (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) :
    modulus.key ≠ array.key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key
    modulus.toCStorageRef array.toCStorageRef same
  cases shapes

/-- A real scalar overwrite preserves every coordinate row without a separate alias premise. -/
lemma wordWrite_read_row (output : CWriteRef ctx (.unsignedWord width))
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index : Fin length) (store : Store ctx) (value : CShape.Word width) :
    (store.write output value).read (rowRead array index) = store.read (rowRead array index) := by
  apply Store.read_write_of_not_mem_storageKeys
  change output.key ∉ [array.key]
  simpa only [List.mem_singleton] using word_array_key_ne output array

/-- Every original scalar arithmetic result preserves the wider stored modulus exactly. -/
lemma wordWrite_read_modulus (output : CWriteRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (store : Store ctx) (value : CShape.Word width) :
    (store.write output value).read (wordRead modulus) = store.read (wordRead modulus) :=
  Store.read_write_other _ _ _ _ (Ne.symm (modulus_word_key_ne modulus output))

/-- A separately named working scalar retains its complete actual word. -/
lemma wordWrite_read_word (output observed : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (value : CShape.Word width) (different : output.key ≠ observed.key) :
    (store.write output value).read (wordRead observed) = store.read (wordRead observed) :=
  Store.read_write_other _ _ _ _ different

/-- The original row overwrite preserves every row of a different physical table array. -/
lemma rowWrite_read_array (written observed : CWriteRef ctx (.fixedVector length (.unsignedWord
      width)))
    (index selected : Fin length) (input : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) (different : written.key ≠ observed.key) :
    (store.applyOp (rowWriteOp written index input)).read (rowRead observed selected) =
      store.read (rowRead observed selected) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  change written.key ∉ [observed.key]
  simpa only [List.mem_singleton] using different

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
