/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame
import Mathlib.Data.List.FinRange

/-!
# Original physical order of the five table columns

The finite column family names the same five actual storage references.
Its keys are injective by the original physical frame separation, without
extra value, arithmetic or runtime assumptions.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Arrays

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Original destination order: negative x, negative y, three x, negative slope and x+1. -/
def column (arrays : Arrays ctx width length) :
    Fin 5 → CWriteRef ctx (.fixedVector length (.unsignedWord width)) :=
  ![arrays.x, arrays.y, arrays.c, arrays.d, arrays.e]

/-- Original physical separation makes the literal finite column keys injective. -/
lemma column_keys_injective (arrays : Arrays ctx width length) :
    Function.Injective (fun index => (arrays.column index).key) := by
  apply List.nodup_ofFn.mp
  simpa [column, List.ofFn_succ] using arrays.distinct

/-- Different actual columns have different physical storage keys. -/
lemma column_key_ne (arrays : Arrays ctx width length) (first second : Fin 5)
    (different : first ≠ second) : (arrays.column first).key ≠ (arrays.column second).key :=
  fun same => different (arrays.column_keys_injective same)

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Arrays
