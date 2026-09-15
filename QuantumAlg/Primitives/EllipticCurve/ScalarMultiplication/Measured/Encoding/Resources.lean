/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Program
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources

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
theorem nativeProgram_eventTrace (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    (nativeProgram width modulus coefficient coordinate).eventTrace =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace := by
  rw [nativeProgram, EncodedBit.FullPlacement.place_eventTrace]
  exact UnitaryCircuit.prodLeft_eventTrace _

private theorem runtime_trace (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    (runtimeProgram width modulus coefficient coordinate).eventTrace =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace := by
  change (nativeProgram width modulus coefficient coordinate).eventTrace ++ [] = _
  exact (List.append_nil _).trans (nativeProgram_eventTrace width modulus coefficient coordinate)

/-- The actual runtime instruction keeps every native event in its original order. -/
theorem coordinateCircuit_eventTrace (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate).Path) :
    (coordinateCircuit width count modulus coefficient coordinate).eventTrace path =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace := by
  obtain ⟨original, rfl⟩ := (ContextUnion.frameLocalPathEquiv
    (originalCircuit width modulus coefficient coordinate) (by trivial)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)).surjective path
  exact (ContextUnion.frameLocal_eventTrace _ _ _ _ original).trans
    (runtime_trace width modulus coefficient coordinate)

/-- Actual event multiplicities equal the original multiplier's full native ledger. -/
theorem coordinateCircuit_cost (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate).Path) :
    (coordinateCircuit width count modulus coefficient coordinate).resourcePool path =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventCost := by
  exact (congrArg ResourcePool.ofList
    (coordinateCircuit_eventTrace width count modulus coefficient coordinate path)).trans
      (UnitaryCircuit.ofList_eventTrace_eq_eventCost _)

/-- One coordinate conversion meets the independent original native multiplier allowance. -/
theorem coordinateCircuit_budget (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate).Path) :
    (coordinateCircuit width count modulus coefficient coordinate).resourcePool path ≤
      MAU.Multiplication.Gidney.nativeBudget width := by
  rw [coordinateCircuit_cost]
  exact MAU.Multiplication.Gidney.gidneyUnitMultiplication_native_bound _ _ _

/-- Every native event-duration assignment follows the same actual multiplier schedule. -/
theorem coordinateCircuit_depth_exact (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (duration : Resource.Event .quantum → Nat)
    (path : (coordinateCircuit width count modulus coefficient coordinate).Path) :
    (coordinateCircuit width count modulus coefficient coordinate).depth duration path =
      (MAU.Multiplication.Gidney.program width modulus coefficient).evaluatedEventDepth
        duration := by
  obtain ⟨original, rfl⟩ := (ContextUnion.frameLocalPathEquiv
    (originalCircuit width modulus coefficient coordinate) (by trivial)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)).surjective path
  refine (ContextUnion.frameLocal_depth _ _ _ _ duration original).trans ?_
  change (nativeProgram width modulus coefficient coordinate).evaluatedEventDepth duration + 0 = _
  rw [Nat.add_zero, nativeProgram, EncodedBit.FullPlacement.place_evaluatedEventDepth]
  exact UnitaryCircuit.prodLeft_evaluatedEventDepth _ _

/-- The independent native event envelope also bounds unit-duration serial depth. -/
theorem coordinateCircuit_depth (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate).Path) :
    (coordinateCircuit width count modulus coefficient coordinate).depth (fun _ => 1) path ≤
      MAU.Multiplication.Gidney.eventBound width := by
  rw [coordinateCircuit_depth_exact]
  exact MAU.Multiplication.Gidney.gidneyUnitMultiplication_depth_bound _ _ _

/-- Pair conversion emits two actual consecutive native multiplier traces. -/
theorem pairCircuit_eventTrace (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient).Path) :
    (pairCircuit width count modulus coefficient).eventTrace path =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace ++
        (MAU.Multiplication.Gidney.program width modulus coefficient).eventTrace := by
  change (coordinateCircuit width count modulus coefficient .x).eventTrace path.1 ++
    (coordinateCircuit width count modulus coefficient .y).eventTrace path.2 = _
  rw [coordinateCircuit_eventTrace, coordinateCircuit_eventTrace]

/-- Both calls are charged independently, with no metadata-only conversion allowance. -/
theorem pairCircuit_budget (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient).Path) :
    (pairCircuit width count modulus coefficient).resourcePool path ≤
      MAU.Multiplication.Gidney.nativeBudget width +
        MAU.Multiplication.Gidney.nativeBudget width := by
  change ResourcePool.ofList ((coordinateCircuit width count modulus coefficient .x).eventTrace
    path.1 ++ (coordinateCircuit width count modulus coefficient .y).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (coordinateCircuit_budget _ _ _ _ _ path.1)
    (coordinateCircuit_budget _ _ _ _ _ path.2)

/-- Serial conversion of X then Y pays both original multiplier depth envelopes. -/
theorem pairCircuit_depth (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient).Path) :
    (pairCircuit width count modulus coefficient).depth (fun _ => 1) path ≤
      2 * MAU.Multiplication.Gidney.eventBound width := by
  change (coordinateCircuit width count modulus coefficient .x).depth (fun _ => 1) path.1 +
    (coordinateCircuit width count modulus coefficient .y).depth (fun _ => 1) path.2 ≤ _
  rw [two_mul]
  exact Nat.add_le_add (coordinateCircuit_depth _ _ _ _ _ path.1)
    (coordinateCircuit_depth _ _ _ _ _ path.2)

private theorem local_resident (width count : Nat)
    (code : Circuit (readyContext width count) (readyContext width count))
    (supported : code.IsLocal) (path : code.Path) :
    code.peakResidentSpace path = readySpace width count := by
  have upper := code.peakResidentSpace_le_of_visited path (readySpace width count) (by
    intro visited present
    rw [ContextUnion.local_visited code supported path visited present,
      readyContext_resident_exact])
  have lower := code.residentSpace_le_peak_of_visited path (readyContext width count)
    (ContextUnion.local_pre_mem code supported path)
  rw [readyContext_resident_exact] at lower
  exact le_antisymm upper lower

private theorem local_auxiliary (width count : Nat)
    (code : Circuit (readyContext width count) (readyContext width count))
    (supported : code.IsLocal) (path : code.Path) :
    code.peakAuxiliarySpace path = readySpace width count := by
  have upper := code.peakAuxiliarySpace_le_of_visited path (readySpace width count) (by
    intro visited present
    rw [ContextUnion.local_visited code supported path visited present,
      readyContext_auxiliary_exact])
  have lower := code.auxiliarySpace_le_peak_of_visited path (readyContext width count)
    (ContextUnion.local_pre_mem code supported path)
  rw [readyContext_auxiliary_exact] at lower
  exact le_antisymm upper lower

/-- Coordinate conversion keeps the complete original and indexed resident capacity. -/
theorem coordinateCircuit_resident (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate).Path) :
    (coordinateCircuit width count modulus coefficient coordinate).peakResidentSpace path =
      readySpace width count :=
  local_resident _ _ _ (coordinateCircuit_isLocal _ _ _ _ _) path

/-- Coordinate conversion preserves the same fixed-role auxiliary capacity,
including result cells. -/
theorem coordinateCircuit_auxiliary (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width count modulus coefficient coordinate).Path) :
    (coordinateCircuit width count modulus coefficient coordinate).peakAuxiliarySpace path =
      readySpace width count :=
  local_auxiliary _ _ _ (coordinateCircuit_isLocal _ _ _ _ _) path

/-- Both coordinate calls share one complete resident workspace. -/
theorem pairCircuit_resident (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient).Path) :
    (pairCircuit width count modulus coefficient).peakResidentSpace path = readySpace width count :=
  local_resident _ _ _ (pairCircuit_isLocal _ _ _ _) path

/-- Reusing A for both calls adds no bank to the actual auxiliary peak. -/
theorem pairCircuit_auxiliary (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width count modulus coefficient).Path) :
    (pairCircuit width count modulus coefficient).peakAuxiliarySpace path =
      readySpace width count :=
  local_auxiliary _ _ _ (pairCircuit_isLocal _ _ _ _) path

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
