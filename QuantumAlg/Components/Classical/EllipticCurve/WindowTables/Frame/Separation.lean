/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.ReadWrite
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Structural separation of scalar words and reused arrays

An actual sealed context cannot give the same storage key to incompatible
closed shapes. Thus every scalar arithmetic output is separate from every
complete table array, without adding an external disjointness assumption.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- A scalar word and a complete array are different physical classical cells by their shapes. -/
lemma word_array_key_ne (word : CWriteRef ctx (.unsignedWord width))
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) :
    word.key ≠ array.key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key word.toCStorageRef array.toCStorageRef same
  cases shapes

/-- The separately widened stored modulus is different from every scalar field word. -/
lemma modulus_word_key_ne (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (word : CWriteRef ctx (.unsignedWord width)) : modulus.key ≠ word.key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key
    modulus.toCStorageRef word.toCStorageRef same
  have widths := CShape.unsignedWord.inj shapes
  omega

/-- A paid existing-array overwrite leaves every scalar word intact. -/
lemma rowWrite_read_word (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index : Fin length) (value : CInputRef ctx (.unsignedWord width))
    (word : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (store.applyOp (rowWriteOp array index value)).read (.storage word.toCStorageRef) =
      store.read (.storage word.toCStorageRef) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  change array.key ∉ [word.key]
  simpa only [List.mem_singleton] using Ne.symm (word_array_key_ne word array)

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
