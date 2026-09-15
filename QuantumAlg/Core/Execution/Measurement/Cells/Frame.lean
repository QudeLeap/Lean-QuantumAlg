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

/-- Actual Z writes preserve every structural read outside their real destination keys. -/
theorem writeMeasurementPath_read_input {ctx : RuntimeCtx .quantum} {shape : CShape}
    (readouts : List (ZReadout ctx)) (input : CInputRef ctx shape)
    (separate : ∀ item ∈ readouts, item.output.key ∉ input.storageKeys)
    (store : Store ctx) (path : (measurementSequence readouts).Path) :
    (writeMeasurementPath readouts store path).read input = store.read input := by
  induction input with
  | storage ref =>
      exact writeMeasurementPath_read_unwritten readouts ref
        (fun item present same => separate item present (List.mem_singleton.mpr same)) store path
  | product left right leftIH rightIH =>
      exact congrArg₂ CShape.Value.product
        (leftIH (fun item present member => separate item present
          (List.mem_append_left _ member)))
        (rightIH (fun item present member => separate item present
          (List.mem_append_right _ member)))
  | fixedVector entries entriesIH =>
      apply congrArg CShape.Value.fixedVector
      funext index
      apply entriesIH index
      intro item present member
      exact separate item present (List.mem_flatten.mpr
        ⟨(entries index).storageKeys, List.mem_ofFn.mpr ⟨index, rfl⟩, member⟩)
  | first input ih => exact congrArg CShape.Value.first (ih separate)
  | second input ih => exact congrArg CShape.Value.second (ih separate)
  | vectorGet input index ih => exact congrArg (fun value => value.get index) (ih separate)
  | bitsGet input index ih => exact congrArg (fun value => value.bitGet index) (ih separate)
  | wordBitGet input index ih => exact congrArg (fun value => value.wordBitGet index) (ih separate)

end Circuit

namespace Execution.MeasurementCells

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}

/-- Lifting an old structural read through the actual allocator keeps exactly its old keys. -/
theorem liftInput_storageKeys (dimension : ℕ+) (input : CInputRef ctx shape) (count : Nat) :
    (liftInput dimension input count).storageKeys = input.storageKeys := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [liftInput, CInputRef.storageKeys_underRetained, ih]

/-- Lifting an old writable reference changes no storage identity. -/
theorem liftWrite_key (dimension : ℕ+) (ref : CWriteRef ctx shape) (count : Nat) :
    (liftWrite dimension ref count).key = ref.key := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- Every actual new finite cell is separate from every old structurally read key. -/
theorem reference_not_mem_liftInput (dimension : ℕ+) (input : CInputRef ctx shape)
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
