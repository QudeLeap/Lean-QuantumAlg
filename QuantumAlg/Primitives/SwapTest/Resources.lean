/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.SwapTest.Execution
import all QuantumAlg.Primitives.SwapTest.Construction
import all QuantumAlg.Primitives.SwapTest.Specification
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Space
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Depth.EventCount

/-!
# Independent native resource bounds for the same elementary SWAP test

Preparation, every H and Toffoli occurrence, and the actual stored Z result
all belong to one run. The original input words and control remain live.
-/

namespace QuantumAlg.SwapTest

noncomputable section

open Execution

private theorem preparation_event :
    (OwnedQubitPrefix.zeroPreparation 1).event =
      Resource.Event.preparation
        { family := "builtin", name := "computational-basis", parameters := [1, 2, 0] } := rfl

private theorem readout_event (width : Nat) :
    Circuit.zEvent
      ((post width).quantumLayout.wire (HadamardTest.readout (width + width)).wire).dimension =
      .measurement { family := "builtin", name := "z", parameters := [2] } := by
  rw [show (HadamardTest.readout (width + width)).wire =
    HadamardTest.controlWire (width + width) from rfl, HadamardTest.controlWire_dimension]
  rfl

/-- Every actual path has exactly the independently stated elementary event ledger. -/
theorem code_events (width : Nat) (path : (code width).Path) :
    (code width).resourcePool path = eventBudget width := by
  simp only [Circuit.resourcePool, code, beforeMeasurement, HadamardTest.readoutCode,
    OwnedQubitPrefix.prepareCode, Circuit.measurementSequence, Circuit.eventTrace,
    List.append_nil, nativeProgram, UnitaryCircuit.reindex_eventTrace,
    sourceCircuit_eventTrace, preparation_event, readout_event]
  simp only [eventBudget, ResourcePool.ofList, List.append_assoc, List.cons_append, List.nil_append]

private theorem program_depth_le (width : Nat) :
    (nativeProgram width).evaluatedEventDepth (fun _ => 1) ≤ 3 * width + 2 := by
  calc
    _ ≤ DepthExpr.costEval (fun _ => 1) (nativeProgram width).eventDepth :=
      DepthExpr.depthEval_le_costEval (fun _ => 1) (nativeProgram width).eventDepth
    _ = (nativeProgram width).eventCost.card :=
      (DepthExpr.unitCost_eq_eventPool_card (nativeProgram width).eventDepth).trans
        (congrArg Multiset.card (UnitaryCircuit.resourcesFromEventDepth_eq_eventCost _))
    _ = 3 * width + 2 := by
      rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeProgram,
        UnitaryCircuit.reindex_eventTrace, sourceCircuit_eventTrace]
      simp only [ResourcePool.ofList, Multiset.coe_card, List.length_append,
        List.length_singleton, List.length_replicate]
      omega

/-- The actual dependency depth is bounded by the full unit-event count. -/
theorem code_depth (width : Nat) (path : (code width).Path) :
    (code width).depth (fun _ => 1) path ≤ 3 * width + 4 := by
  change (1 + ((nativeProgram width).evaluatedEventDepth (fun _ => 1) + 0)) +
    (1 + 0) ≤ 3 * width + 4
  have bounded := program_depth_le width
  omega

/-- Actual resident space counts all input, prepared and retained resources. -/
theorem code_residentSpace (width : Nat) (path : (code width).Path) :
    (code width).peakResidentSpace path ≤ spaceBudget width := by
  change (HadamardTest.code (swapRegistersOp width)).peakResidentSpace path ≤
    HadamardTest.spaceBudget (width + width)
  exact HadamardTest.code_residentSpace (swapRegistersOp width) path

/-- Owned input words remain included in the actual auxiliary-role capacity. -/
theorem code_auxiliarySpace (width : Nat) (path : (code width).Path) :
    (code width).peakAuxiliarySpace path ≤ spaceBudget width := by
  change (HadamardTest.code (swapRegistersOp width)).peakAuxiliarySpace path ≤
    HadamardTest.spaceBudget (width + width)
  exact HadamardTest.code_auxiliarySpace (swapRegistersOp width) path

end

end QuantumAlg.SwapTest
