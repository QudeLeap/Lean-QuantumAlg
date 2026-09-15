/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Native costs of the actual measured numerator reset

The same run executes its parallel H layer, sequential Z writes, and the
X sequence selected from those actual stored values. The independent
allowance includes at most n events at each of these three native
coordinates. Its serial dependency includes measurement before correction.
The full live frame includes both inputs, all EEA auxiliaries and the n
retained finite result cells [LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorReset

noncomputable section

open Execution MAU.Inversion.SharedEEA

/-- Independent native allowance for H, Z measurement and the possible literal X corrections. -/
def budget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton WalshHadamard.hadamardEvent width +
    (width • ResourcePool.singleton (Circuit.zEvent 2) +
      width • ResourcePool.singleton (.gate (.builtin "x")))

private theorem hadamard_cost (width : Nat) (path : (hadamard width).Path) :
    (hadamard width).resourcePool path =
      ResourcePool.singleton WalshHadamard.hadamardEvent width := by
  change ResourcePool.ofList (NumeratorRuntime.program width (hadamardMember width)).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, NumeratorRuntime.program_cost]
  have actual : (hadamardMember width).eventCost = (WalshHadamard.hadamardLayer width).eventCost :=
    UnitaryCircuit.prodRight_eventCost _
  exact actual.trans (WalshHadamard.hadamardLayer_eventCost width)

/-- The exact actual trace satisfies the independent three-coordinate allowance. -/
theorem code_budget (width : Nat) (path : (code width).Path) :
    (code width).resourcePool path ≤ budget width := by
  change ResourcePool.ofList ((hadamard width).eventTrace path.1 ++
    ((NumeratorMeasurement.measure width).eventTrace path.2.1 ++
      (reset width).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add (hadamard_cost width path.1).le
    (add_le_add (NumeratorMeasurement.measurement_resources width path.2.1).le
      (reset_budget width path.2.2))

private theorem placement_depth (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (duration : Resource.Event .quantum → Nat) :
    (NumeratorRuntime.program width body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  change body.evaluatedEventDepth duration + 0 = _
  exact Nat.add_zero _

private theorem hadamard_depth (width : Nat) (path : (hadamard width).Path) :
    (hadamard width).depth (fun _ => 1) path = if width = 0 then 0 else 1 := by
  change (NumeratorRuntime.program width (hadamardMember width)).evaluatedEventDepth
    (fun _ => 1) = _
  rw [placement_depth]
  have actual : (hadamardMember width).evaluatedEventDepth (fun _ => 1) =
      (WalshHadamard.hadamardLayer width).evaluatedEventDepth (fun _ => 1) :=
    UnitaryCircuit.prodRight_evaluatedEventDepth _ _
  rw [actual, UnitaryCircuit.evaluatedEventDepth, WalshHadamard.hadamardLayer_eventDepth]
  exact WalshHadamard.parallelHadamardEventDepth_unit_depth width

private theorem reset_depth (width : Nat) (path : (reset width).Path) :
    (reset width).depth (fun _ => 1) path ≤ width := by
  change (NumeratorRuntime.program width (member width path.1)).evaluatedEventDepth
    (fun _ => 1) ≤ _
  rw [placement_depth]
  have actual : (member width path.1).evaluatedEventDepth (fun _ => 1) =
      (StoredWordReset.program (outcome path.1)).evaluatedEventDepth (fun _ => 1) :=
    UnitaryCircuit.prodRight_evaluatedEventDepth _ _
  rw [actual, StoredWordReset.storedWordReset_depth]
  exact EncodedBit.Word.BasisLoad.basisLoad_count_le _

/-- Measurement-to-correction dependence is part of the same serial unit-duration bound. -/
theorem code_depth (width : Nat) (path : (code width).Path) :
    (code width).depth (fun _ => 1) path ≤ 1 + 2 * width := by
  change (hadamard width).depth (fun _ => 1) path.1 +
    ((NumeratorMeasurement.measure width).depth (fun _ => 1) path.2.1 +
      (reset width).depth (fun _ => 1) path.2.2) ≤ _
  have measured : (NumeratorMeasurement.measure width).depth (fun _ => 1) path.2.1 = width :=
    (Circuit.measurementSequence_unitDepth (NumeratorMeasurement.readouts width) path.2.1).trans
      List.length_ofFn
  rw [hadamard_depth, measured]
  have resetBound := reset_depth width path.2.2
  split <;> omega

/-- The same actual paths keep every input, EEA history wire and retained finite result cell. -/
theorem visited (width : Nat) (path : (code width).Path) :
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
theorem code_resident (width : Nat) (path : (code width).Path) :
    (code width).peakResidentSpace path ≤ (NumeratorMeasurement.context width).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro ctx present
  rw [visited] at present
  have same : ctx = NumeratorMeasurement.context width := by simpa using present
  rw [same]

end

end QuantumAlg.MeasuredUncompute.NumeratorReset
