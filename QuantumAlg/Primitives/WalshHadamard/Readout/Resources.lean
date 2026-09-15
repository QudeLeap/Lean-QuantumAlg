/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Components.Oracle.Common
import Mathlib.Data.List.OfFn

/-!
# Exact native Walsh-Hadamard query readout events and depth

These calculations use the actual preparation values, original executable
query circuit, measured wires and packing instruction. They verify the
independently stated formulas, including the width-zero execution with no
measurements and one actual packing event.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

open QuantumAlg.Execution

private theorem preparation_label_value (n : Nat) :
    (prodEquiv ((0 : Fin (2 ^ n)), (1 : Fin (2 ^ 1)))).val = 1 := by
  simp [prodEquiv]

private theorem preparation_query_value (n : Nat) (index : Fin n) :
    ((inputPreparation n).value index.castSucc).val = 0 := by
  change (finTwoEquiv.symm
    ((prodEquiv ((0 : Fin (2 ^ n)), (1 : Fin (2 ^ 1)))).val.testBit index.castSucc.rev.val)).val = 0
  rw [preparation_label_value]
  have positive : 0 < index.castSucc.rev.val := by
    simp only [Fin.rev, Fin.val_castSucc]
    omega
  have zeroBit : Nat.testBit 1 index.castSucc.rev.val = false := by
    simpa only [pow_zero] using
      (Nat.testBit_two_pow_of_ne (n := 0) (m := index.castSucc.rev.val) (by omega))
  rw [zeroBit]
  rfl

private theorem preparation_target_value (n : Nat) :
    ((inputPreparation n).value (Fin.last n)).val = 1 := by
  change (finTwoEquiv.symm
    ((prodEquiv ((0 : Fin (2 ^ n)), (1 : Fin (2 ^ 1)))).val.testBit (Fin.last n).rev.val)).val = 1
  rw [preparation_label_value]
  have lastPosition : (Fin.last n).rev.val = 0 := by simp
  rw [lastPosition]
  rfl

theorem inputPreparation_event (n : Nat) : (inputPreparation n).event =
    .preparation
      { family := "builtin"
        name := "computational-basis"
        parameters := (n + 1) ::
          (List.replicate (n + 1) 2 ++ (List.replicate n 0 ++ [1])) } := by
  have dimensions : (runtimeLayout n).dimensions.map PNat.val = List.replicate (n + 1) 2 := by
    change (List.ofFn (fun _ : Fin (n + 1) => (2 : ℕ+))).map PNat.val = _
    rw [List.map_ofFn]
    exact List.ofFn_const (n + 1) 2
  have values : List.ofFn (fun index => ((inputPreparation n).value index).val) =
      List.replicate n 0 ++ [1] := by
    rw [List.ofFn_succ']
    simp only [preparation_query_value, preparation_target_value, List.ofFn_const,
      List.concat_eq_append]
  change Resource.Event.preparation
    { family := "builtin", name := "computational-basis",
      parameters := (n + 1) ::
        ((runtimeLayout n).dimensions.map PNat.val ++
          List.ofFn (fun index => ((inputPreparation n).value index).val)) } = _
  rw [dimensions, values]

private theorem program_pool {n : Nat} (f : WalshHadamard.Oracle n) :
    ResourcePool.ofList (program f).eventTrace =
      (2 * n + 1) • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        ResourcePool.singleton (.quantumSubroutine (xorOracleSubroutineLabel n).quantum) := by
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, program,
    UnitaryCircuit.reindex_eventCost, WalshHadamard.circuit_eventCost]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (WalshHadamard.eventPool n) = ResourcePool.count event _
  simp only [WalshHadamard.eventPool, WalshHadamard.hadamardEvent,
    WalshHadamard.xorOracleEvent, ResourcePool.count_add, ResourcePool.count_singleton,
    ResourcePool.count_nsmul]
  by_cases hadamard : Resource.Event.gate (.builtin "hadamard") = event
  · simp only [hadamard, if_true, mul_one]
    omega
  · simp only [hadamard, if_false, mul_zero, zero_add, add_zero]

private theorem measurement_pool (n : Nat)
    (path : (Circuit.measurementSequence (readouts n)).Path) :
    ResourcePool.ofList ((Circuit.measurementSequence (readouts n)).eventTrace path) =
      n • ResourcePool.singleton (Circuit.zEvent 2) := by
  change (Circuit.measurementSequence (readouts n)).resourcePool path = _
  rw [Circuit.measurementSequence_qubit_resourcePool (readouts n) (readouts_qubits n),
    readouts_length]

private theorem packing_trace (n : Nat) :
    (packing n).eventTrace =
      [.classicalOperation (.nominalEncoding (.packFiniteBits n))] :=
  ClassicalOp.eventTrace_packFiniteBits n _ _ _

private theorem allocation_trace (n : Nat) (path : (allocationCode n).Path) :
    (allocationCode n).eventTrace path = [] :=
  MeasurementCells.allocate_eventTrace (resultContext n) 2 n path.2

/-- The actual path emits exactly the independent preparation, gate, measurement
and packing pool. -/
theorem code_events {n : Nat} (f : WalshHadamard.Oracle n) (path : (code f).Path) :
    (code f).resourcePool path =
      ResourcePool.singleton (.preparation
        { family := "builtin"
          name := "computational-basis"
          parameters := (n + 1) ::
            (List.replicate (n + 1) 2 ++ (List.replicate n 0 ++ [1])) }) +
      ((2 * n + 1) • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        ResourcePool.singleton (.quantumSubroutine (xorOracleSubroutineLabel n).quantum)) +
      (n • ResourcePool.singleton
        (.measurement { family := "builtin", name := "z", parameters := [2] }) +
        ResourcePool.singleton (.classicalOperation (.nominalEncoding (.packFiniteBits n)))) := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    preparationCode, allocation_trace, Circuit.eventTrace,
    List.append_nil, ResourcePool.ofList_append, ResourcePool.ofList_cons,
    ResourcePool.ofList_nil, add_zero, inputPreparation_event, program_pool,
    measurement_pool, packing_trace]
  rfl

private theorem program_depth {n : Nat} (f : WalshHadamard.Oracle n) :
    (program f).evaluatedEventDepth (fun _ => 1) = if n = 0 then 2 else 3 := by
  change DepthExpr.depthEval (fun _ => 1) (WalshHadamard.circuit f).eventDepth = _
  rw [WalshHadamard.circuit_eventDepth]
  exact WalshHadamard.eventCriticalPath_unit_depth n

/-- Actual unit-event depth includes preparation, every sequential measurement and packing. -/
theorem code_depth {n : Nat} (f : WalshHadamard.Oracle n) (path : (code f).Path) :
    (code f).depth (fun _ => 1) path = 1 + (if n = 0 then 2 else 3) + n + 1 := by
  change (1 + ((program f).evaluatedEventDepth (fun _ => 1) +
    (0 + (MeasurementCells.allocate (resultContext n) 2 n).depth
      (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (readouts n)).depth (fun _ => 1) path.2.1 + 1) = _
  rw [MeasurementCells.allocate_depth, Circuit.measurementSequence_unitDepth,
    readouts_length, program_depth]
  omega

end

end QuantumAlg.WalshHadamard.Readout
