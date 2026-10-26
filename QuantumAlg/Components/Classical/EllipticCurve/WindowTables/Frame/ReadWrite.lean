/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Exact existing-array row writes

One real vector-write instruction preserves every other row, including the
identity address when a batch visits only nonzero indices. Structural input
references read the original Store before the instruction overwrites its
actual array destination.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Every actual array element is the original element except the selected paid overwrite. -/
lemma rowWrite_read (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index : Fin length) (value : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) (observed : Fin length) :
    (store.applyOp (rowWriteOp array index value)).read (rowRead array observed) =
      if observed = index then store.read value else store.read (rowRead array observed) := by
  have written : (store.applyOp (rowWriteOp array index value)).read
      (.storage array.toCStorageRef) = CShape.vectorWrite
        (store.read (.storage array.toCStorageRef)) index (store.read value) :=
    Store.read_applyOp_output store (rowWriteOp array index value)
  change ((store.applyOp (rowWriteOp array index value)).read
    (.storage array.toCStorageRef)).get observed = _
  rw [written]
  change Function.update (store.read (.storage array.toCStorageRef)).get index
    (store.read value) observed = _
  by_cases same : observed = index
  · subst observed
    simp only [Function.update_self, if_true]
  · rw [Function.update_of_ne same, if_neg same]
    rfl

/-- The selected actual result row is read from the incoming Store, even when it aliases input. -/
lemma rowWrite_read_same (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index : Fin length) (value : CInputRef ctx (.unsignedWord width)) (store : Store ctx) :
    (store.applyOp (rowWriteOp array index value)).read (rowRead array index) =
      store.read value := by
  rw [rowWrite_read, if_pos rfl]

/-- A protected row, in particular address zero, survives every different real row overwrite. -/
lemma rowWrite_read_other (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index : Fin length) (value : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) (observed : Fin length) (different : observed ≠ index) :
    (store.applyOp (rowWriteOp array index value)).read (rowRead array observed) =
      store.read (rowRead array observed) := by
  rw [rowWrite_read, if_neg different]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
