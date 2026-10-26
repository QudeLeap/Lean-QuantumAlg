/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Existing storage supplied to the five-table builder

Five large arrays, four scalar words and one loaded modulus are reused.
The source base coordinates and zero, one and curve coefficient are actual
existing references. Separation protects these reads throughout all array
and scalar overwrites; their values are established by paid caller loaders.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

variable {kind : ProblemKind}

/-- Literal existing storage for one window; no table values enter the program constructor. -/
structure TableFrame (ctx : RuntimeCtx kind) (width length : Nat) where
  arrays : Arrays ctx width length
  work : Work ctx width
  modulus : CWriteRef ctx (.unsignedWord (width + 1))
  zero : CInputRef ctx (.unsignedWord width)
  one : CInputRef ctx (.unsignedWord width)
  curveA : CInputRef ctx (.unsignedWord width)
  baseX : CInputRef ctx (.unsignedWord width)
  baseY : CInputRef ctx (.unsignedWord width)
  protectedReads : ∀ input ∈ [zero, one, curveA, baseX, baseY],
    ∀ key ∈ [arrays.x.key, arrays.y.key, arrays.c.key, arrays.d.key, arrays.e.key,
      work.product.key, work.inverse.key, work.temporary.key, work.slope.key],
      key ∉ input.storageKeys

namespace TableFrame

variable {ctx : RuntimeCtx kind} {width length : Nat}

/-- C and D are exactly the existing denominator and prefix arrays of the batch engine. -/
def batch (frame : TableFrame ctx width length) : BatchFrame ctx width length where
  denominators := frame.arrays.c
  prefixes := frame.arrays.d
  work := frame.work
  modulus := .storage frame.modulus.toCStorageRef
  one := frame.one
  separate := by
    have absent := (List.nodup_cons.mp
      (List.nodup_cons.mp (List.nodup_cons.mp frame.arrays.distinct).2).2).1
    intro same
    exact absent (by simp [same])

end TableFrame

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
