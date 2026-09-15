/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Layout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame

/-!
# Distinct raw finite samples on one original finite-cyclic bank

Every sample owns its complete pair of finite exponent readouts. The actual
allocator retains all these cells once, and structural vector references
group them by chronological sample and original exponent position. There is
no copied sample value and no second bank. Zero samples still retain the
original prepared quantum bank.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The sample number and exponent position select one distinct retained cell. -/
def cellIndex (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (index : Fin (sampleWidth P)) : Fin (count * sampleWidth P) :=
  finProdFinEquiv (slot, index)

/-- The indexed vector groups consecutive exponent positions within each sample. -/
theorem cellIndex_val (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (index : Fin (sampleWidth P)) :
    (cellIndex P slot index).val = index.val + sampleWidth P * slot.val := rfl

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat)

/-- All raw finite samples coexist above the single original quantum bank. -/
def context : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext base noQuantum P) 2 (count * sampleWidth P)

/-- One actual writable finite destination for one sample and exponent position. -/
def cells (slot : Fin count) (index : Fin (sampleWidth P)) :
    CWriteRef (context base noQuantum P count) (.finite 2) :=
  MeasurementCells.reference (bankContext base noQuantum P) 2 (count * sampleWidth P)
    (cellIndex P slot index)

/-- Recovery consumes each ordered raw sample directly from its actual measurement cells. -/
def samples (slot : Fin count) :
    CInputRef (context base noQuantum P count) (.fixedVector (sampleWidth P) (.finite 2)) :=
  .fixedVector fun index => .storage (cells base noQuantum P count slot index).toCStorageRef

/-- The final raw sample vector is only a structural collection of retained references. -/
def samplesInput : CInputRef (context base noQuantum P count)
    (.fixedVector count (.fixedVector (sampleWidth P) (.finite 2))) :=
  .fixedVector (samples base noQuantum P count)

/-- Original caller operands keep their exact storage identities through both allocations. -/
def liftInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (context base noQuantum P count) shape :=
  MeasurementCells.liftInput 2
    (input.underOwnedLayout base.canonicalFreshKey (bankLayout P) base.canonicalFreshKey_fresh
      (allocationDisjoint base noQuantum P)) (count * sampleWidth P)

/-- Allocating all raw samples changes no wire of the original three-register bank. -/
theorem nativeFiniteCyclicBatch_context_wires :
    (context base noQuantum P count).quantumWires = (bankLayout P).wires := by
  rw [context, MeasurementCells.context_quantumWires]
  exact nativeFiniteCyclic_bankContext_wires base noQuantum P

/-- Distinct sample-position pairs have distinct actual storage destinations. -/
theorem nativeFiniteCyclicBatch_cells_key_injective :
    Function.Injective (fun pair : Fin count × Fin (sampleWidth P) =>
      (cells base noQuantum P count pair.1 pair.2).key) := by
  intro left right same
  exact finProdFinEquiv.injective
    (MeasurementCells.reference_key_injective (bankContext base noQuantum P) 2
      (count * sampleWidth P) same)

/-- Writing any position of one sample cannot overwrite any cell of another sample. -/
theorem nativeFiniteCyclicBatch_cell_not_mem_samples
    (written observed : Fin count) (different : written ≠ observed)
    (index : Fin (sampleWidth P)) :
    (cells base noQuantum P count written index).key ∉
      (samples base noQuantum P count observed).storageKeys := by
  change _ ∉ (List.ofFn (fun position : Fin (sampleWidth P) =>
    [(cells base noQuantum P count observed position).key])).flatten
  intro member
  obtain ⟨keys, listed, present⟩ := List.mem_flatten.mp member
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp listed
  have same := nativeFiniteCyclicBatch_cells_key_injective base noQuantum P count
    (a₁ := (written, index)) (a₂ := (observed, position)) (List.mem_singleton.mp present)
  exact different (congrArg Prod.fst same)

/-- Every newly allocated measurement destination is separate from each original caller read. -/
theorem nativeFiniteCyclicBatch_cell_not_mem_liftInput {shape : CShape}
    (input : CInputRef base shape) (slot : Fin count) (index : Fin (sampleWidth P)) :
    (cells base noQuantum P count slot index).key ∉
      (liftInput base noQuantum P count input).storageKeys :=
  MeasurementCells.reference_not_mem_liftInput 2
    (input.underOwnedLayout base.canonicalFreshKey (bankLayout P) base.canonicalFreshKey_fresh
      (allocationDisjoint base noQuantum P)) (count * sampleWidth P) (cellIndex P slot index)

/-- A real finite write preserves the complete structural value of every other raw sample. -/
theorem nativeFiniteCyclicBatch_write_preserves_sample
    (store : Store (context base noQuantum P count)) (written observed : Fin count)
    (different : written ≠ observed) (index : Fin (sampleWidth P)) (value : Fin 2) :
    (store.write (cells base noQuantum P count written index) (.finite value)).read
        (samples base noQuantum P count observed) =
      store.read (samples base noQuantum P count observed) :=
  Store.read_write_of_not_mem_storageKeys store _ _ _
    (nativeFiniteCyclicBatch_cell_not_mem_samples base noQuantum P count
      written observed different index)

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch
