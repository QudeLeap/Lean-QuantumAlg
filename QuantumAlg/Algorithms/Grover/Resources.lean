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
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits
import all QuantumAlg.Primitives.WalshHadamard
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
open QuantumAlg.ZeroReflection.Workspace

private theorem preparation_pool {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (preparationCode marked k).Path) :
    ResourcePool.ofList ((preparationCode marked k).eventTrace path) =
      totalQubits n k • ResourcePool.singleton (model := model marked)
        (.preparation (2 : ℕ+)) :=
  ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model (Elementary.oracles marked)
    (runtimeLayout (totalQubits n k)) 2 (fun _ => rfl) BitWord.model .empty

private theorem program_pool {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    ResourcePool.ofList ((program marked k).eventTrace BitWord.model .empty) =
      unitaryBudget marked k := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (program marked k) BitWord.model .empty,
    program,
    unitaryOfEqualWires_cost
      (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout
      (preparedContext (totalQubits n k)).quantumLayout
      (prepared_canonical_wires (totalQubits n k)) (Elementary.circuit marked k)]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    ((Elementary.circuit marked k).eventCost BitWord.model .empty) = ResourcePool.count event _
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      change AlgorithmGate.Coordinate at coordinate
      cases coordinate <;>
        rcases n with _ | _ | _ | _ | n <;>
        simp [Elementary.circuit_eventCost, Elementary.unitaryEventPool, unitaryBudget,
          ZeroReflection.elementaryEventPool, ResourcePool.count_add,
          ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | oracle coordinate =>
      change UnitarySource.Coordinate at coordinate
      cases coordinate <;>
        rcases n with _ | _ | _ | _ | n <;>
        simp [Elementary.circuit_eventCost, Elementary.unitaryEventPool, unitaryBudget,
          ZeroReflection.elementaryEventPool, ResourcePool.count_add,
          ResourcePool.count_nsmul, ResourcePool.count_singleton]
  | _ =>
      rcases n with _ | _ | _ | _ | n <;>
        simp [unitaryBudget, ZeroReflection.elementaryEventPool,
          ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton]

private theorem measurement_pool {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := Elementary.oracles marked) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts n k)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := Elementary.oracles marked) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts n k)).eventTrace path) =
      n • ResourcePool.singleton (model := model marked) (.measurement (2 : ℕ+)) := by
  rw [← Circuit.resourcePool,
    Circuit.measurementSequence_qubit_resourcePool (readouts n k) (readouts_qubits n k),
    readouts_length]
  rfl

private theorem allocation_trace {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (allocationCode marked k).Path) : (allocationCode marked k).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (model := model marked) (resultContext n k) 2 n path.2

/-- Every actual path has exactly the independent complete native event pool. -/
theorem code_events {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    (code marked k).resourcePool path = eventBudget marked k := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    Circuit.eventTrace, allocation_trace, List.append_nil, ResourcePool.ofList_append,
    program_pool, measurement_pool]
  rw [preparation_pool marked k path.1.1]
  rfl

private theorem program_depth {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    DepthExpr.depthEval (fun _ => 1) ((program marked k).eventDepth BitWord.model .empty) =
      Elementary.unitaryDepth n k := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  change (Elementary.circuit marked k).evaluatedEventDepth (fun _ => 1) = _
  exact Elementary.circuit_unitDepth marked k

/-- Exact unit-event depth includes each preparation layer, sequential Z write and packing. -/
theorem code_depth_exact {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    (code marked k).depth (fun _ => 1) path =
      (if totalQubits n k = 0 then 0 else 1) + Elementary.unitaryDepth n k + n + 1 := by
  change (DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model (Elementary.oracles marked)
        (runtimeLayout (totalQubits n k)) BitWord.model .empty) +
    (DepthExpr.depthEval (fun _ => 1) ((program marked k).eventDepth BitWord.model .empty) +
      (0 + (MeasurementCells.allocate (model := model marked)
        (resultContext n k) 2 n).depth (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := Elementary.oracles marked) (operations := BitWord.model)
      (classicalOracles := .empty) (readouts n k)).depth
      (fun _ => 1) path.2.1 + 1) = _
  rw [ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model
    (Elementary.oracles marked) (runtimeLayout (totalQubits n k)) 2 (fun _ => rfl)
    BitWord.model .empty, MeasurementCells.allocate_depth,
    Circuit.measurementSequence_unitDepth, readouts_length, program_depth]
  omega

/-- The independent full-cycle depth bound also covers the empty source register. -/
theorem code_depth {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    (code marked k).depth (fun _ => 1) path ≤ depthBudget n k := by
  rw [code_depth_exact]
  unfold depthBudget
  split <;> omega

/-- Every elementary source-reflection occurrence belongs to this actual execution. -/
theorem code_elementaryGateCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((code marked k).resourcePool path) =
        n + k * (2 * n + ZeroReflection.elementaryGateCount n) := by
  rw [code_events]
  rcases n with _ | _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, ZeroReflection.elementaryEventPool,
      ZeroReflection.elementaryGateCount, ResourcePool.weightedCount_add,
      ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton] <;> ring

/-- Exact native single-qubit count of the same complete search execution. -/
theorem code_singleQubitCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    ResourcePool.count (model := model marked) (.gate .singleQubit)
      ((code marked k).resourcePool path) =
        n + k * (2 * n + ZeroReflection.elementarySingleQubitCount n) := by
  rw [code_events]
  rcases n with _ | _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, ZeroReflection.elementaryEventPool,
      ZeroReflection.elementarySingleQubitCount, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton] <;> ring

/-- Exact native CNOT count of the same complete search execution. -/
theorem code_cnotCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    ResourcePool.count (model := model marked) (.gate .cnot)
      ((code marked k).resourcePool path) =
        k * ZeroReflection.elementaryCNOTCount n := by
  rw [code_events]
  rcases n with _ | _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, ZeroReflection.elementaryEventPool,
      ZeroReflection.elementaryCNOTCount, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- Exact native Toffoli count of the same complete search execution. -/
theorem code_toffoliCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    ResourcePool.count (model := model marked) (.gate .toffoli)
      ((code marked k).resourcePool path) =
        k * ZeroReflection.elementaryToffoliCount n := by
  rw [code_events]
  rcases n with _ | _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, ZeroReflection.elementaryEventPool,
      ZeroReflection.elementaryToffoliCount, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton]

/-- The actual run contains exactly k phase queries, with no opaque reflection call. -/
theorem code_queryCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (code marked k).Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .oracle _ => 1 | _ => 0) ((code marked k).resourcePool path) = k := by
  rw [code_events]
  rcases n with _ | _ | _ | _ | n <;>
    simp [eventBudget, unitaryBudget, ZeroReflection.elementaryEventPool,
      ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
      ResourcePool.weightedCount_singleton]

end

end QuantumAlg.GroverSearch
