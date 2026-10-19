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
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Independent native resource bounds for the same complete SWAP test

The complete execution includes preparation, both H operations, each actual
CNOT and Toffoli, and the stored Z result. Every original quantum system remains live.
-/

namespace QuantumAlg.SwapTest

noncomputable section

open Execution

private lemma readout_event (width : Nat) :
    Circuit.zEvent (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (classicalOracles := .empty)
      ((post width).quantumLayout.wire (HadamardTest.readout (width + width)).wire).dimension =
      .measurement (2 : ℕ+) := by
  rw [show (HadamardTest.readout (width + width)).wire =
    HadamardTest.controlWire (width + width) from rfl, HadamardTest.controlWire_dimension]
  rfl

/-- Every actual path has exactly the independently stated complete native event ledger. -/
lemma code_events (width : Nat) (path : (code width).Path) :
    (code width).resourcePool path = eventBudget width := by
  change ResourcePool.ofList
    ((ZeroPreparation.eventTrace AlgorithmGate.model .empty
      (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout ++
      ((nativeProgram width).eventTrace ++ [])) ++
      [Circuit.zEvent (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := .empty) (classicalOracles := .empty)
        ((post width).quantumLayout.wire
          (HadamardTest.readout (width + width)).wire).dimension]) = _
  rw [ZeroPreparation.zeroPreparation_uniform_trace AlgorithmGate.model .empty
    (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout 2 (fun _ => rfl), List.append_nil,
    ResourcePool.ofList_append, ResourcePool.ofList_append,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeProgram,
    Execution.unitaryOfEqualWires_cost, sourceCircuit_eventCost, readout_event]
  rfl

/-- The full depth includes control preparation, all gates and the actual measurement. -/
lemma code_depth (width : Nat) (path : (code width).Path) :
    (code width).depth (fun _ => 1) path ≤ 3 * width + 4 := by
  change (1 + ((sourceCircuit width).evaluatedEventDepth (fun _ => 1) + 0)) +
    (1 + 0) ≤ 3 * width + 4
  rw [sourceCircuit_depth]
  omega

/-- Actual resident space counts all input, prepared and retained resources. -/
lemma code_residentSpace (width : Nat) (path : (code width).Path) :
    (code width).peakResidentSpace path ≤ spaceBudget width := by
  change (HadamardTest.code (width + width)).peakResidentSpace path ≤
    HadamardTest.spaceBudget (width + width)
  exact HadamardTest.code_residentSpace (width + width) path

/-- Owned input words remain included in the actual auxiliary-role capacity. -/
lemma code_auxiliarySpace (width : Nat) (path : (code width).Path) :
    (code width).peakAuxiliarySpace path ≤ spaceBudget width := by
  change (HadamardTest.code (width + width)).peakAuxiliarySpace path ≤
    HadamardTest.spaceBudget (width + width)
  exact HadamardTest.code_auxiliarySpace (width + width) path

end

end QuantumAlg.SwapTest
