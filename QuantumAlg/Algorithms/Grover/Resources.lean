/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Algorithms.Grover.Elementary.Resources
import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Algorithms.Grover.Specification
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Components.Oracle.Common
import all QuantumAlg.Components.Oracle.ZeroReflection
import Mathlib.Data.List.OfFn

/-!
# Grover's exact native events and depth

The source query and actual elementary reflection sequences provide the
unitary events and parallel-layer depth. The complete execution additionally
charges preparation of every search and selected work system, the n actual
source Z writes and one packing opcode. Every equality observes the same
interpreter trace and an independently defined parameter-only budget.
-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.Execution

private theorem preparation_value (n : Nat) (index : Fin n) :
    ((inputPreparation n).value index).val = 0 := by
  change (finTwoEquiv.symm ((0 : Fin (2 ^ n)).val.testBit index.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

theorem inputPreparation_event (n : Nat) :
    (inputPreparation n).event = preparationEvent n := by
  have dimensions : (runtimeLayout n).dimensions.map PNat.val = List.replicate n 2 := by
    change (List.ofFn (fun _ : Fin n => (2 : ℕ+))).map PNat.val = _
    rw [List.map_ofFn]
    exact List.ofFn_const n 2
  have values : List.ofFn (fun index => ((inputPreparation n).value index).val) =
      List.replicate n 0 := by
    simp only [preparation_value, List.ofFn_const]
  change Resource.Event.preparation
    { family := "builtin", name := "computational-basis",
      parameters := n ::
        ((runtimeLayout n).dimensions.map PNat.val ++
          List.ofFn (fun index => ((inputPreparation n).value index).val)) } = _
  rw [dimensions, values]
  rfl

private theorem program_pool {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    ResourcePool.ofList (program marked k).eventTrace = Elementary.unitaryEventPool n k := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, program,
    UnitaryCircuit.reindex_eventCost, Elementary.circuit_eventCost]

private theorem measurement_pool (n k : Nat)
    (path : (Circuit.measurementSequence (readouts n k)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (readouts n k)).eventTrace path) =
      n • ResourcePool.singleton (Circuit.zEvent 2) := by
  change (Circuit.measurementSequence (readouts n k)).resourcePool path = _
  rw [Circuit.measurementSequence_qubit_resourcePool (readouts n k) (readouts_qubits n k),
    readouts_length]

private theorem packing_trace (n k : Nat) :
    (packing n k).eventTrace =
      [.classicalOperation (.nominalEncoding (.packFiniteBits n))] :=
  ClassicalOp.eventTrace_packFiniteBits n _ _ _

private theorem allocation_trace (n k : Nat) (path : (allocationCode n k).Path) :
    (allocationCode n k).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (resultContext n k) 2 n path.2

/-- Every actual path has exactly the independent complete native event pool. -/
theorem code_events {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    (code marked k).resourcePool path = eventBudget n k := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    preparationCode, allocation_trace, Circuit.eventTrace,
    List.append_nil, ResourcePool.ofList_append, ResourcePool.ofList_cons,
    ResourcePool.ofList_nil, add_zero, inputPreparation_event, program_pool,
    measurement_pool, packing_trace]
  rfl

private theorem program_depth {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (program marked k).evaluatedEventDepth (fun _ => 1) = Elementary.unitaryDepth n k := by
  change (Elementary.circuit marked k).evaluatedEventDepth (fun _ => 1) = _
  exact Elementary.circuit_unitDepth marked k

/-- Exact unit-event depth includes preparation, each sequential Z write and final packing. -/
theorem code_depth {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    (code marked k).depth (fun _ => 1) path = depthBudget n k := by
  change (1 + ((program marked k).evaluatedEventDepth (fun _ => 1) +
    (0 + (MeasurementCells.allocate (resultContext n k) 2 n).depth
      (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (readouts n k)).depth (fun _ => 1) path.2.1 + 1) = _
  rw [MeasurementCells.allocate_depth, Circuit.measurementSequence_unitDepth,
    readouts_length, program_depth]
  unfold depthBudget
  omega

/-- Every elementary source-reflection occurrence belongs to this actual execution. -/
theorem code_elementaryGateCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((code marked k).resourcePool path) =
        n + k * (2 * n + ZeroReflection.elementaryGateCount n) := by
  let weight : Resource.Event .quantum → Nat := fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight ((code marked k).resourcePool path) =
    Elementary.unitaryGateCount n k
  have actual := Elementary.circuit_gateCount marked k
  rw [Elementary.circuit_eventCost] at actual
  have programCount : ResourcePool.weightedCount weight (Elementary.unitaryEventPool n k) =
      Elementary.unitaryGateCount n k := by
    refine Eq.trans ?_ actual
    apply congrArg (fun assignment : Resource.Event .quantum → Nat =>
      ResourcePool.weightedCount assignment (Elementary.unitaryEventPool n k))
    funext event
    cases event <;> rfl
  rw [code_events]
  simp only [eventBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_singleton, ResourcePool.weightedCount_nsmul]
  rw [programCount]
  dsimp only [weight, preparationEvent]
  ring

/-- The actual run contains exactly k phase queries and no reflected opaque subroutine. -/
theorem code_queryCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .quantumSubroutine _ => 1 | _ => 0) ((code marked k).resourcePool path) = k := by
  let weight : Resource.Event .quantum → Nat := fun event => match event with
    | .quantumSubroutine _ => 1 | _ => 0
  change ResourcePool.weightedCount weight ((code marked k).resourcePool path) = k
  have actual := Elementary.circuit_queryCount marked k
  rw [Elementary.circuit_eventCost] at actual
  have programCount :
      ResourcePool.weightedCount weight (Elementary.unitaryEventPool n k) = k := by
    refine Eq.trans ?_ actual
    apply congrArg (fun assignment : Resource.Event .quantum → Nat =>
      ResourcePool.weightedCount assignment (Elementary.unitaryEventPool n k))
    funext event
    cases event <;> rfl
  rw [code_events]
  simp only [eventBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_singleton, ResourcePool.weightedCount_nsmul]
  rw [programCount]
  dsimp only [weight, preparationEvent]
  ring

end

end QuantumAlg.GroverSearch
