/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Program
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Native conversion events and complete resident workspace

Actual placement and framing preserve the original multiplier's ordered
native events and serial depth. Two coordinate conversions charge two
independent multiplier budgets while retaining one complete workspace.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open MeasuredUncompute Execution

/-- Placing one native multiplier emits precisely its original ordered events. -/
lemma nativeProgram_eventTrace (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    (nativeProgram width modulus coefficient coordinate).eventTrace =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace := by
  rw [nativeProgram, EncodedBit.FullPlacement.place_eventTrace]
  exact UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventTrace _ _

private lemma runtime_trace (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    (runtimeProgram width modulus coefficient coordinate).eventTrace =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace := by
  rw [runtimeProgram, UnitaryCircuit.placeAt_eventTrace]
  exact nativeProgram_eventTrace width modulus coefficient coordinate

/-- The actual runtime instruction keeps every native event in its original order. -/
lemma coordinateCircuit_eventTrace {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate allowAllocation).Path) :
    (coordinateCircuit width count modulus coefficient coordinate allowAllocation).eventTrace path =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace := by
  exact (ContextUnion.contextUnion_frameUnitary_eventTrace
    (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
    (runtimeProgram width modulus coefficient coordinate) _ _).trans
      (runtime_trace width modulus coefficient coordinate)

/-- Actual event multiplicities equal the original multiplier's full native ledger. -/
lemma coordinateCircuit_cost {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate allowAllocation).Path) :
    (coordinateCircuit width count modulus coefficient coordinate
      allowAllocation).resourcePool path =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventCost := by
  exact (congrArg ResourcePool.ofList
    (coordinateCircuit_eventTrace (allowAllocation := allowAllocation) width count modulus
      coefficient coordinate path)).trans
      (UnitaryCircuit.ofList_eventTrace_eq_eventCost _)

/-- One coordinate conversion meets the independent original native multiplier allowance. -/
lemma coordinateCircuit_budget {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate allowAllocation).Path) :
    (coordinateCircuit width count modulus coefficient coordinate
      allowAllocation).resourcePool path ≤
      MAU.Multiplication.Gidney.nativeBudget width := by
  rw [coordinateCircuit_cost]
  exact MAU.Multiplication.Gidney.gidneyUnitMultiplication_native_bound _ _ _

/-- Every native event-duration assignment follows the same actual multiplier schedule. -/
lemma coordinateCircuit_depth_exact {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (coordinateCircuit width count modulus coefficient coordinate allowAllocation).Path) :
    (coordinateCircuit width count modulus coefficient coordinate
      allowAllocation).depth duration path =
      (MAU.Multiplication.Gidney.program width modulus coefficient).evaluatedEventDepth
        duration := by
  refine (ContextUnion.contextUnion_frameUnitary_evaluatedEventDepth
    (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
    (runtimeProgram width modulus coefficient coordinate) _ _ duration).trans ?_
  change (runtimeProgram width modulus coefficient coordinate).evaluatedEventDepth duration = _
  rw [runtimeProgram, UnitaryCircuit.placeAt_evaluatedEventDepth,
    nativeProgram, EncodedBit.FullPlacement.place_evaluatedEventDepth]
  exact UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth _ _ _

/-- The independent native event envelope also bounds unit-duration serial depth. -/
lemma coordinateCircuit_depth {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate allowAllocation).Path) :
    (coordinateCircuit width count modulus coefficient coordinate
      allowAllocation).depth (fun _ => 1) path ≤
      MAU.Multiplication.Gidney.eventBound width := by
  rw [coordinateCircuit_depth_exact]
  exact MAU.Multiplication.Gidney.gidneyUnitMultiplication_depth_bound _ _ _

/-- Pair conversion emits two actual consecutive native multiplier traces. -/
lemma pairCircuit_eventTrace {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient allowAllocation).Path) :
    (pairCircuit width count modulus coefficient allowAllocation).eventTrace path =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace ++
        (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace := by
  change (coordinateCircuit width count modulus coefficient .x allowAllocation).eventTrace path.1 ++
    (coordinateCircuit width count modulus coefficient .y allowAllocation).eventTrace path.2 = _
  rw [coordinateCircuit_eventTrace, coordinateCircuit_eventTrace]

/-- Both calls are charged independently, with no metadata-only conversion allowance. -/
lemma pairCircuit_budget {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient allowAllocation).Path) :
    (pairCircuit width count modulus coefficient allowAllocation).resourcePool path ≤
      MAU.Multiplication.Gidney.nativeBudget width +
        MAU.Multiplication.Gidney.nativeBudget width := by
  change ResourcePool.ofList ((coordinateCircuit width count modulus coefficient .x
    allowAllocation).eventTrace
    path.1 ++ (coordinateCircuit width count modulus coefficient .y allowAllocation).eventTrace
      path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (coordinateCircuit_budget (allowAllocation := allowAllocation) _ _ _ _ _ path.1)
    (coordinateCircuit_budget (allowAllocation := allowAllocation) _ _ _ _ _ path.2)

/-- Serial conversion of X then Y pays both original multiplier depth envelopes. -/
lemma pairCircuit_depth {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient allowAllocation).Path) :
    (pairCircuit width count modulus coefficient allowAllocation).depth (fun _ => 1) path ≤
      2 * MAU.Multiplication.Gidney.eventBound width := by
  change (coordinateCircuit width count modulus coefficient .x allowAllocation).depth (fun _ => 1)
    path.1 +
    (coordinateCircuit width count modulus coefficient .y allowAllocation).depth (fun _ => 1) path.2
      ≤ _
  rw [two_mul]
  exact Nat.add_le_add (coordinateCircuit_depth (allowAllocation := allowAllocation) _ _ _ _ _
    path.1)
    (coordinateCircuit_depth (allowAllocation := allowAllocation) _ _ _ _ _ path.2)

/-- Coordinate conversion keeps the complete original and indexed resident capacity. -/
lemma coordinateCircuit_resident {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate allowAllocation).Path) :
    (coordinateCircuit width count modulus coefficient coordinate
      allowAllocation).peakResidentSpace path =
      readySpace width count := by
  change SpacePool.max (readyContext width count).residentSpace 0 = _
  rw [SpacePool.max_zero, readyContext_resident_exact]

/-- Coordinate conversion preserves the same fixed-role auxiliary capacity,
including result cells. -/
lemma coordinateCircuit_auxiliary {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate allowAllocation).Path) :
    (coordinateCircuit width count modulus coefficient coordinate
      allowAllocation).peakAuxiliarySpace path =
      readySpace width count := by
  change SpacePool.max (readyContext width count).auxiliarySpace 0 = _
  rw [SpacePool.max_zero, readyContext_auxiliary_exact]

/-- Both coordinate calls share one complete resident workspace. -/
lemma pairCircuit_resident {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient allowAllocation).Path) :
    (pairCircuit width count modulus coefficient allowAllocation).peakResidentSpace path =
      readySpace width count := by
  exact (Circuit.peakResidentSpace_seq
    (coordinateCircuit width count modulus coefficient .x allowAllocation)
    (coordinateCircuit width count modulus coefficient .y allowAllocation) path).trans
    ((congrArg₂ SpacePool.max
      (coordinateCircuit_resident (allowAllocation := allowAllocation)
        width count modulus coefficient .x path.1)
      (coordinateCircuit_resident (allowAllocation := allowAllocation)
        width count modulus coefficient .y path.2)).trans (SpacePool.max_self _))

/-- Reusing A for both calls adds no bank to the actual auxiliary peak. -/
lemma pairCircuit_auxiliary {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient allowAllocation).Path) :
    (pairCircuit width count modulus coefficient allowAllocation).peakAuxiliarySpace path =
      readySpace width count := by
  exact (Circuit.peakAuxiliarySpace_seq
    (coordinateCircuit width count modulus coefficient .x allowAllocation)
    (coordinateCircuit width count modulus coefficient .y allowAllocation) path).trans
    ((congrArg₂ SpacePool.max
      (coordinateCircuit_auxiliary (allowAllocation := allowAllocation)
        width count modulus coefficient .x path.1)
      (coordinateCircuit_auxiliary (allowAllocation := allowAllocation)
        width count modulus coefficient .y path.2)).trans (SpacePool.max_self _))

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
