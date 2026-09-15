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

private theorem preparation_event :
    (OwnedQubitPrefix.zeroPreparation 1).event =
      Resource.Event.preparation
        { family := "builtin", name := "computational-basis", parameters := [1, 2, 0] } := rfl

private theorem readout_event (width : Nat) :
    Circuit.zEvent ((post width).quantumLayout.wire (readout width).wire).dimension =
      .measurement { family := "builtin", name := "z", parameters := [2] } := by
  rw [show (readout width).wire = controlWire width from rfl, controlWire_dimension]
  rfl

/-- Every actual path has exactly the complete independently specified native ledger. -/
theorem code_events {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (path : (code unitary).Path) :
    (code unitary).resourcePool path = eventBudget width := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, readoutCode,
    OwnedQubitPrefix.prepareCode, Circuit.measurementSequence, Circuit.eventTrace,
    List.append_nil, nativeProgram, UnitaryCircuit.reindex_eventTrace,
    sourceCircuit_eventTrace, preparation_event, readout_event]
  rfl

private theorem program_depth_le {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (nativeProgram unitary).evaluatedEventDepth (fun _ => 1) ≤ 3 := by
  calc
    _ ≤ DepthExpr.costEval (fun _ => 1) (nativeProgram unitary).eventDepth :=
      DepthExpr.depthEval_le_costEval (fun _ => 1) (nativeProgram unitary).eventDepth
    _ = (nativeProgram unitary).eventCost.card :=
      (DepthExpr.unitCost_eq_eventPool_card (nativeProgram unitary).eventDepth).trans
        (congrArg Multiset.card (UnitaryCircuit.resourcesFromEventDepth_eq_eventCost _))
    _ = 3 := by
      rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeProgram,
        UnitaryCircuit.reindex_eventTrace, sourceCircuit_eventTrace]
      rfl

/-- The actual dependency depth fits five unit-duration native operations. -/
theorem code_depth {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (path : (code unitary).Path) : (code unitary).depth (fun _ => 1) path ≤ 5 := by
  change (1 + ((nativeProgram unitary).evaluatedEventDepth (fun _ => 1) + 0)) +
    (1 + 0) ≤ 5
  have bounded := program_depth_le unitary
  omega

end

end QuantumAlg.HadamardTest
