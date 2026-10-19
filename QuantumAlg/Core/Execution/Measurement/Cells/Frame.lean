/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Structural inputs outside the actual measurement cells

Closed structural reads retain their complete values when their real keys
are outside the Z-write destinations. Allocating new finite cells preserves
the old input keys and separates every new measurement destination from
them. These are wiring facts about the existing allocator and real writes;
they do not constrain quantum states or prescribe measurement outcomes.
-/

namespace QuantumAlg

namespace Circuit

open Execution

variable {allowAllocation : Bool}

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}

/-- Actual Z writes preserve every structural read outside their real destination keys. -/
lemma writeMeasurementPath_read_input {ctx : RuntimeCtx .quantum} {shape : CShape}
    (readouts : List (ZReadout ctx)) (input : CInputRef ctx shape)
    (separate : ∀ item ∈ readouts, item.output.key ∉ input.storageKeys)
    (store : Store ctx)
    (path : (measurementSequence (allowAllocation := allowAllocation) (gates := gates)
      (oracles := oracles) (operations := operations)
      (classicalOracles := classicalOracles) readouts).Path) :
    (writeMeasurementPath (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      readouts store path).read input = store.read input := by
  induction readouts generalizing store with
  | nil => rfl
  | cons head tail ih =>
      exact (ih (fun item present => separate item (.tail head present))
        (store.write head.output (.finite path.1)) path.2).trans
        (Store.read_write_of_not_mem_storageKeys store head.output (.finite path.1)
          input (separate head (.head tail)))

end Circuit

namespace Execution.MeasurementCells

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}

/-- Lifting an old structural read through the actual allocator keeps exactly its old keys. -/
lemma liftInput_storageKeys (dimension : ℕ+) (input : CInputRef ctx shape) (count : Nat) :
    (liftInput dimension input count).storageKeys = input.storageKeys := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [liftInput, CInputRef.storageKeys_underRetained, ih]

/-- Lifting an old writable reference changes no storage identity. -/
lemma liftWrite_key (dimension : ℕ+) (ref : CWriteRef ctx shape) (count : Nat) :
    (liftWrite dimension ref count).key = ref.key := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- Every actual new finite cell is separate from every old structurally read key. -/
lemma reference_not_mem_liftInput (dimension : ℕ+) (input : CInputRef ctx shape)
    (count : Nat) (index : Fin count) :
    (reference ctx dimension count index).key ∉ (liftInput dimension input count).storageKeys := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ?_) index
      · exact CInputRef.fresh_not_mem_storageKeys_underRetained
          (liftInput dimension input count) (context ctx dimension count).canonicalFreshKey
          (.finite dimension) (context ctx dimension count).canonicalFreshKey_fresh
      · change (reference ctx dimension count previous).key ∉
          ((liftInput dimension input count).underRetained
            (context ctx dimension count).canonicalFreshKey (.finite dimension)
            (context ctx dimension count).canonicalFreshKey_fresh).storageKeys
        rw [CInputRef.storageKeys_underRetained]
        exact ih previous

end Execution.MeasurementCells

end QuantumAlg
