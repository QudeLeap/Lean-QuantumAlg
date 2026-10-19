/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset.Matrix
import all QuantumAlg.Core.Execution.Measurement.Cells.Borrowed
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Reused raw cells and the complete untouched Simon store

The mathematical projection removes only the raw measurement-cell coordinates.
It does not release physical storage. The original caller data and every
packed sample slot remain in the projected store. Those coordinates together
with all n actual raw-cell values determine the complete live store.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

variable {allowAllocation : Bool} {oracles : OracleModel}

/-- Only the actual n measurement heads are omitted from this mathematical observation. -/
def originalStore (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (n count : Nat) : Store (context base noQuantum n count) →
      Store (bankContext base noQuantum n count) :=
  MeasurementCells.originalStore 2 n

private lemma cells_store_ext {ctx : RuntimeCtx .quantum} (width : Nat)
    (first second : Store (MeasurementCells.context ctx 2 width))
    (original : MeasurementCells.originalStore 2 width first =
      MeasurementCells.originalStore 2 width second)
    (values : ∀ index : Fin width,
      first.read (.storage (MeasurementCells.reference ctx 2 width index).toCStorageRef) =
      second.read (.storage (MeasurementCells.reference ctx 2 width index).toCStorageRef)) :
    first = second := by
  induction width with
  | zero => exact original
  | succ width ih =>
      obtain ⟨first⟩ := first
      obtain ⟨second⟩ := second
      apply congrArg Store.mk
      apply Prod.ext
      · exact values 0
      · have tail := ih (Store.mk first.2) (Store.mk second.2) original
          (fun index => values index.succ)
        exact congrArg Store.cells tail

/-- The projected original store and every reused result determine the complete live store. -/
lemma store_ext (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (n count : Nat) (first second : Store (context base noQuantum n count))
    (original : originalStore base noQuantum n count first =
      originalStore base noQuantum n count second)
    (values : ∀ index : Fin n,
      first.read (.storage (cells base noQuantum n count index).toCStorageRef) =
      second.read (.storage (cells base noQuantum n count index).toCStorageRef)) :
    first = second := cells_store_ext n first second original values

/-- Each real raw-cell write preserves the entire caller-and-packed-sample store. -/
lemma originalStore_write (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (n count : Nat) {shape : CShape} (output : CWriteRef (context base noQuantum n count) shape)
    (raw : ∃ index, output.key = (cells base noQuantum n count index).key)
    (store : Store (context base noQuantum n count)) (value : shape.Value) :
    originalStore base noQuantum n count (store.write output value) =
      originalStore base noQuantum n count store := by
  apply Store.store_eq_of_storage_reads
  intro observedShape input
  have separate : output.key ∉ (MeasurementCells.liftInput 2 (.storage input) n).storageKeys := by
    obtain ⟨index, same⟩ := raw
    rw [same]
    exact MeasurementCells.reference_not_mem_liftInput 2 (.storage input) n index
  exact (MeasurementCells.originalStore_read 2 n (store.write output value) (.storage input)).trans
    ((Store.read_write_of_not_mem_storageKeys store output value
      (MeasurementCells.liftInput 2 (.storage input) n) separate).trans
        (MeasurementCells.originalStore_read 2 n store (.storage input)).symm)

/-- A whole actual measurement path preserves the complete old store if it writes only raw cells. -/
lemma originalStore_writePath (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (n count : Nat)
    (items : List (ZReadout (context base noQuantum n count)))
    (raw : ∀ item ∈ items, ∃ index, item.output.key = (cells base noQuantum n count index).key)
    (store : Store (context base noQuantum n count))
    (path : (Circuit.measurementSequence (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty) items).Path) :
    originalStore base noQuantum n count
      (Circuit.writeMeasurementPath (allowAllocation := allowAllocation)
        (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := .empty) items store path) =
      originalStore base noQuantum n count store := by
  induction items generalizing store with
  | nil => rfl
  | cons head tail ih =>
      exact (ih (fun item present => raw item (.tail head present))
        (store.write head.output (.finite path.1)) path.2).trans
        (originalStore_write base noQuantum n count head.output (raw head (.head tail))
          store (.finite path.1))

/-- The actual writes in either batch preserve the entire old store, not the overwritten raw cells.
-/
lemma originalStore_written (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (n count : Nat) (half : Fin 2) (store : Store (context base noQuantum n count))
    (basis : (context base noQuantum n count).register.Index) :
    originalStore base noQuantum n count
      (writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count half store basis) = originalStore base noQuantum n count store := by
  apply originalStore_writePath
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact ⟨index, QubitReadouts.readout_key _ _ _⟩

/-- Allocating the ordinary raw-cell heads and observing underneath recovers the exact old store. -/
lemma originalStore_push {ctx : RuntimeCtx .quantum} (width : Nat) (store : Store ctx) :
    MeasurementCells.originalStore 2 width (MeasurementCells.pushStore 2 width store) = store :=
      by
  induction width with
  | zero => rfl
  | succ width ih => exact ih

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset
