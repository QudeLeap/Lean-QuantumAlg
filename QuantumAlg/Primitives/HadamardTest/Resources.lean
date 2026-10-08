/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Construction
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Primitives.HadamardTest.Native
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Depth.EventCount

/-!
# Exact Hadamard-test native events and independent depth

One actual preparation, two Hadamards, one controlled source query and one
stored Z measurement form the complete execution [AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

open Execution

private theorem readout_event {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    Circuit.zEvent (gates := AlgorithmGate.model)
      (oracles := UnitarySource.model unitary true) (operations := .empty)
      (classicalOracles := .empty)
      ((post width).quantumLayout.wire (readout width).wire).dimension =
      .measurement (2 : ℕ+) := by
  rw [show (readout width).wire = controlWire width from rfl, controlWire_dimension]
  rfl

/-- Every actual path has exactly the complete independently specified native ledger. -/
theorem code_events {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (path : (code unitary).Path) :
    (code unitary).resourcePool path = eventBudget unitary := by
  change ResourcePool.ofList
    ((ZeroPreparation.eventTrace AlgorithmGate.model (UnitarySource.model unitary true)
      (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout ++
      ((nativeProgram unitary).eventTrace ++ [])) ++
      [Circuit.zEvent (gates := AlgorithmGate.model)
      (oracles := UnitarySource.model unitary true) (operations := .empty)
      (classicalOracles := .empty)
        ((post width).quantumLayout.wire (readout width).wire).dimension]) = _
  rw [ZeroPreparation.zeroPreparation_uniform_trace AlgorithmGate.model
    (UnitarySource.model unitary true) (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout
    2 (fun _ => rfl), List.append_nil,
    ResourcePool.ofList_append, ResourcePool.ofList_append,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeProgram,
    Execution.unitaryOfEqualWires_cost, sourceCircuit, Native.hadamardTestNative_eventCost,
    readout_event]
  rfl

private theorem program_depth_le {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (nativeProgram unitary).evaluatedEventDepth (fun _ => 1) ≤ 3 :=
  le_of_eq (Native.hadamardTestNative_unit_depth unitary)

/-- The actual dependency depth fits five unit-duration native operations. -/
theorem code_depth {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (path : (code unitary).Path) : (code unitary).depth (fun _ => 1) path ≤ 5 := by
  change (1 + ((nativeProgram unitary).evaluatedEventDepth (fun _ => 1) + 0)) +
    (1 + 0) ≤ 5
  have bounded := program_depth_le unitary
  omega

end

end QuantumAlg.HadamardTest
