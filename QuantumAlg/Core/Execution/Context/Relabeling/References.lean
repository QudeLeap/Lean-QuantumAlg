/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.Context.Relabeling
import all QuantumAlg.Core.Execution.Context.Union.References
import all QuantumAlg.Core.Execution.Context.Relabeling.Layout

/-!
# Actual references under injective context placement

Each reference follows the original computational entry position. Its key uses
the prescribed storage embedding, while its role, shape and write permission
remain unchanged. Compound reads retain their complete structural operands.
-/

namespace QuantumAlg.Execution.ContextRelabeling

variable {kind : ProblemKind}
  (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)

private def slot {entry : RuntimeEntry kind} {entries : List (RuntimeEntry kind)} :
    RuntimeEntrySlot entry entries →
      RuntimeEntrySlot (entry.relabel keys physical)
        (entries.map (RuntimeEntry.relabel keys physical))
  | .here => .here
  | .there next => .there (slot next)

/-- The same entry position now names its mapped key with its original role and shape. -/
def storage {ctx : RuntimeCtx kind} {shape : CShape} (ref : CStorageRef ctx shape) :
    CStorageRef (ctx.relabel keys physical) shape where
  key := keys ref.key
  role := ref.role
  slot := slot keys physical ref.slot

/-- Placement preserves the role-based permission of each actual writable cell. -/
def writable {ctx : RuntimeCtx kind} {shape : CShape} (ref : CWriteRef ctx shape) :
    CWriteRef (ctx.relabel keys physical) shape where
  toCStorageRef := storage keys physical ref.toCStorageRef
  writable := ref.writable

/-- All structural input operands read from their correspondingly placed cells. -/
def input {ctx : RuntimeCtx kind} {shape : CShape} (ref : CInputRef ctx shape) :
    CInputRef (ctx.relabel keys physical) shape :=
  ContextUnion.mapInput (storage keys physical) ref

/-- The mapped reference uses exactly the declared storage embedding. -/
lemma storage_key {ctx : RuntimeCtx kind} {shape : CShape} (ref : CStorageRef ctx shape) :
    (storage keys physical ref).key = keys ref.key := rfl

/-- The original role is retained, including read-only borrowed inputs. -/
lemma storage_role {ctx : RuntimeCtx kind} {shape : CShape} (ref : CStorageRef ctx shape) :
    (storage keys physical ref).role = ref.role := rfl

/-- Writable cells use the same storage-key map as read operands. -/
lemma writable_key {ctx : RuntimeCtx kind} {shape : CShape} (ref : CWriteRef ctx shape) :
    (writable keys physical ref).key = keys ref.key := rfl

noncomputable section

/-- Name the mapped actual writable cell at the corresponding system's proved dimension. -/
def measurement (ctx : RuntimeCtx .quantum) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    CWriteRef (ctx.relabel keys physical)
      (.finite ((ctx.relabel keys physical).quantumLayout.wire
        (positions ctx keys physical wire)).dimension) :=
  Eq.mp (congrArg
    (fun dimension : ℕ+ => CWriteRef (ctx.relabel keys physical) (.finite dimension))
    (positions_dimension ctx keys physical wire).symm) (writable keys physical output)

end

end QuantumAlg.Execution.ContextRelabeling
