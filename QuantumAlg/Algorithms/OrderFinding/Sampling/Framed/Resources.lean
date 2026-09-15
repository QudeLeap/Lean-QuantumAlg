/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Budget
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Source.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Context
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Storage
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Execution
import all QuantumAlg.Algorithms.OrderFinding.Construction
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits
import Mathlib.Data.List.OfFn

/-!
# Exact complete order-finding sampling events and depth

The actual original unitary, Z writes and packing have the independently
stated native counts on every run path, including zero-width registers.
-/

namespace QuantumAlg.OrderFinding.Sampling.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

private theorem program_pool {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    ResourcePool.ofList (nativeProgram ctx noQuantum A).eventTrace =
      unitaryEventBudget N x t n := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeProgram,
    UnitaryCircuit.reindex_eventCost, orderFindingCircuit_eventCost, QFTCircuit_eventCost_eq]
  rfl

private theorem measurement_pool (t n : Nat)
    (path : (Circuit.measurementSequence (readouts ctx noQuantum t n)).Path) :
    ResourcePool.ofList
      ((Circuit.measurementSequence (readouts ctx noQuantum t n)).eventTrace path) =
      t • ResourcePool.singleton (Circuit.zEvent 2) := by
  change (Circuit.measurementSequence (readouts ctx noQuantum t n)).resourcePool path = _
  rw [Circuit.measurementSequence_qubit_resourcePool
    (readouts ctx noQuantum t n) (readouts_qubits ctx noQuantum t n),
    readouts_length]

private theorem packing_trace (t n : Nat) :
    (packing ctx noQuantum t n).eventTrace =
      [.classicalOperation (.nominalEncoding (.packFiniteBits t))] :=
  ClassicalOp.eventTrace_packFiniteBits t _ _ _

private theorem allocation_trace (t n : Nat) (path : (allocationCode ctx noQuantum t n).Path) :
    (allocationCode ctx noQuantum t n).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (resultContext ctx noQuantum t n) 2 t path.2

/-- Every actual path has exactly the independent complete native event pool. -/
theorem code_events {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code ctx noQuantum A).Path) :
    (code ctx noQuantum A).resourcePool path = eventBudget N x t n := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    preparationCode, allocation_trace, Circuit.eventTrace,
    List.append_nil, ResourcePool.ofList_append, ResourcePool.ofList_cons,
    ResourcePool.ofList_nil, add_zero, inputPreparation_event, program_pool,
    measurement_pool, packing_trace]
  rfl

private theorem program_depth {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    (nativeProgram ctx noQuantum A).evaluatedEventDepth (fun _ => 1) = unitaryDepth t := by
  change (orderFindingCircuit A).evaluatedEventDepth (fun _ => 1) = _
  rw [orderFindingCircuit, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, preparation_depth, readout_depth]
  rfl

/-- Exact unit-event depth includes preparation, each sequential Z write and final packing. -/
theorem code_depth {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code ctx noQuantum A).Path) :
    (code ctx noQuantum A).depth (fun _ => 1) path = depthBudget t := by
  change (1 + ((nativeProgram ctx noQuantum A).evaluatedEventDepth (fun _ => 1) +
    (0 + (MeasurementCells.allocate (resultContext ctx noQuantum t n) 2 t).depth
      (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (readouts ctx noQuantum t n)).depth (fun _ => 1) path.2.1 + 1) = _
  rw [MeasurementCells.allocate_depth, Circuit.measurementSequence_unitDepth,
    readouts_length, program_depth]
  unfold depthBudget
  omega

/-- The complete sample retains the original single modular-exponentiation query. -/
theorem code_modExpCount {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code ctx noQuantum A).Path) :
    ResourcePool.count (modExpEvent N x t n) ((code ctx noQuantum A).resourcePool path) = 1 := by
  rw [code_events]
  simp [eventBudget, unitaryEventBudget, basisPreparationEvent, modExpEvent,
    WalshHadamard.hadamardEvent]

end

end QuantumAlg.OrderFinding.Sampling.Framed
