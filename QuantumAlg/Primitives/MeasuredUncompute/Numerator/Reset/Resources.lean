/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Time

/-!
# Native costs of the actual measured numerator reset

The same run executes its parallel H layer, sequential Z writes, and the
parallel X layer selected from those actual stored values. The independent
allowance includes at most n events at each of these three native
coordinates. Its serial dependency includes measurement before correction.
The full live frame includes both inputs, all EEA auxiliaries and the n
retained finite result cells [LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorReset

noncomputable section

open Execution MAU.Inversion.SharedEEA

/-- Independent native allowance for H, Z measurement and the possible literal X corrections. -/
def budget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  width • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) +
    (width • ResourcePool.singleton (Circuit.zEvent (gates := AlgorithmGate.model)
      (oracles := .empty) 2 .empty .empty) +
      width • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit))

private lemma hadamard_cost (width : Nat) (path : (hadamard width).Path) :
    (hadamard width).resourcePool path =
      width • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) := by
  change ResourcePool.ofList (NumeratorRuntime.program width (hadamardMember width)).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, NumeratorRuntime.program_cost]
  change (UnitaryCircuit.onCanonicalBinarySuffix (encoding width).width
    (Gate.HadamardLayer.circuit .empty width)).eventCost = _
  exact (UnitaryCircuit.onCanonicalBinarySuffix_eventCost (encoding width).width
    (Gate.HadamardLayer.circuit .empty width)).trans
      (Gate.HadamardLayer.hadamardLayer_circuit_eventCost .empty width)

/-- The exact actual trace satisfies the independent three-coordinate allowance. -/
lemma code_budget (width : Nat) (path : (code width).Path) :
    (code width).resourcePool path ≤ budget width := by
  change ResourcePool.ofList ((hadamard width).eventTrace path.1 ++
    ((NumeratorMeasurement.measure width).eventTrace path.2.1 ++
      (reset width).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add (hadamard_cost width path.1).le
    (add_le_add (NumeratorMeasurement.measurement_resources width path.2.1).le
      (reset_budget width path.2.2))

private lemma placement_depth (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (NumeratorRuntime.program width body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  unfold UnitaryCircuit.evaluatedEventDepth NumeratorRuntime.program
  rw [Execution.unitaryOfEqualWires_depth, InverseRuntimeFrame.program]
  exact congrArg (DepthExpr.depthEval duration)
    (UnitaryCircuit.placeAt_eventDepth _ _ _ _ body)

private lemma hadamard_depth (width : Nat) (path : (hadamard width).Path) :
    (hadamard width).depth (fun _ => 1) path = if width = 0 then 0 else 1 := by
  change (NumeratorRuntime.program width (hadamardMember width)).evaluatedEventDepth
    (fun _ => 1) = _
  rw [placement_depth]
  change (UnitaryCircuit.onBinarySuffix (encoding width).width
    (Gate.HadamardLayer.circuit .empty width)).evaluatedEventDepth (fun _ => 1) = _
  rw [UnitaryCircuit.unitaryCircuit_onBinarySuffix_evaluatedEventDepth]
  exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth .empty width

private lemma reset_depth (width : Nat) (path : (reset width).Path) :
    (reset width).depth (fun _ => 1) path ≤ if width = 0 then 0 else 1 := by
  change (NumeratorRuntime.program width (member width path.1)).evaluatedEventDepth
    (fun _ => 1) ≤ _
  rw [placement_depth]
  change (UnitaryCircuit.onCanonicalBinarySuffix (encoding width).width
    (NumeratorResetParallel.program (outcome path.1))).evaluatedEventDepth
      (fun _ => 1) ≤ _
  rw [UnitaryCircuit.onCanonicalBinarySuffix_evaluatedEventDepth]
  exact NumeratorResetParallel.program_unitDepth _

/-- Generic unit duration still charges each actual Z write between the two native layers. -/
lemma code_unitDepth (width : Nat) (path : (code width).Path) :
    (code width).depth (fun _ => 1) path ≤ if width = 0 then 0 else width + 2 := by
  change (hadamard width).depth (fun _ => 1) path.1 +
    ((NumeratorMeasurement.measure width).depth (fun _ => 1) path.2.1 +
      (reset width).depth (fun _ => 1) path.2.2) ≤ _
  have measured : (NumeratorMeasurement.measure width).depth (fun _ => 1) path.2.1 = width :=
    (Circuit.measurementSequence_unitDepth (NumeratorMeasurement.readouts width) path.2.1).trans
      List.length_ofFn
  rw [hadamard_depth, measured]
  have resetBound := reset_depth width path.2.2
  split_ifs at * <;> omega

/-- The earlier unit-duration allowance remains valid for the improved actual schedule. -/
lemma code_depth (width : Nat) (path : (code width).Path) :
    (code width).depth (fun _ => 1) path ≤ 1 + 2 * width := by
  have actual := code_unitDepth width path
  split_ifs at actual <;> omega

/-- Canonical quantum time charges the H and selected X layers, retaining all Z-write events. -/
lemma code_quantumTime (width : Nat) (path : (code width).Path) :
    (code width).quantumTime path ≤ if width = 0 then 0 else 2 := by
  change (hadamard width).quantumTime path.1 +
    ((NumeratorMeasurement.measure width).quantumTime path.2.1 +
      (reset width).quantumTime path.2.2) ≤ _
  have measured : (NumeratorMeasurement.measure width).quantumTime path.2.1 = 0 := by
    refine (Circuit.measurementSequence_depth (NumeratorMeasurement.readouts width)
      Resource.Event.quantumDuration path.2.1).trans ?_
    simp [Circuit.zEvent, Resource.Event.quantumDuration]
  rw [measured, Nat.zero_add]
  have first := Circuit.quantumTime_le_unitDepth (hadamard width) path.1
  rw [hadamard_depth] at first
  have second := (Circuit.quantumTime_le_unitDepth (reset width) path.2.2).trans
    (reset_depth width path.2.2)
  split_ifs at * <;> omega

/-- The same actual paths keep every input, EEA history wire and retained finite result cell. -/
lemma visited (width : Nat) (path : (code width).Path) :
    (code width).visitedContexts path =
      [NumeratorMeasurement.context width] ++
        (List.replicate (width + 1) (NumeratorMeasurement.context width) ++
          [NumeratorMeasurement.context width]) := by
  change [_] ++ ((NumeratorMeasurement.measure width).visitedContexts path.2.1 ++ [_]) = _
  have measured := Circuit.measurementSequence_visitedContexts
    (NumeratorMeasurement.readouts width) path.2.1
  change (NumeratorMeasurement.measure width).visitedContexts path.2.1 = _ at measured
  rw [measured]
  simp only [NumeratorMeasurement.readouts, QubitReadouts.readouts, List.length_ofFn]

/-- Resident space includes all real finite results and keeps the entire physical frame. -/
lemma code_resident (width : Nat) (path : (code width).Path) :
    (code width).peakResidentSpace path ≤ (NumeratorMeasurement.context width).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro ctx present
  rw [visited] at present
  have same : ctx = NumeratorMeasurement.context width := by simpa using present
  rw [same]

end

end QuantumAlg.MeasuredUncompute.NumeratorReset
