/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Reflection.Resources
import all QuantumAlg.Components.Encoded.BitGates.Reflection.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.PhaseProgram
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Coordinates
import all QuantumAlg.Core.Base.Accounting.Weighted
import Mathlib.Tactic.IntervalCases

/-!
# Independent elementary budgets of controlled positive source reflection

A source of width zero, one or two uses zero, three or eight gates and no
work position. Larger sources borrow one different actual phase position;
the exact restored action uses 2n X gates, two H gates, one control Z and
the balanced n-control Toffoli schedule. The independent formulas are
proved equal to the actual native event pool and sequential depth.
-/

namespace QuantumAlg.ZeroReflection

noncomputable section

open EncodedBit.Word.OneDirtyLayout

/-- Native elementary multiplicities of the selected controlled source synthesis. -/
def controlledElementaryEventPool : Nat → ResourcePool .quantum
  | 0 => 0
  | 1 => 2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
      ResourcePool.singleton (.gate (.builtin "cnot"))
  | 2 => 4 • ResourcePool.singleton (.gate (.builtin "x")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
      ResourcePool.singleton (.gate (.builtin "toffoli")) +
      ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z"))
  | extra + 3 => (2 * (extra + 3)) • ResourcePool.singleton (.gate (.builtin "x")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
      gateCount (extra + 3) • ResourcePool.singleton (.gate (.builtin "toffoli")) +
      ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z"))

/-- Independent count and unit-event depth, including the exact controlled global minus. -/
public def controlledElementaryGateCount : Nat → Nat
  | 0 => 0
  | 1 => 3
  | 2 => 8
  | extra + 3 => 2 * (extra + 3) + gateCount (extra + 3) + 3

/-- The empty controlled reflection is the identity and has no gate occurrences. -/
@[simp] public theorem controlledElementaryGateCount_zero :
    controlledElementaryGateCount 0 = 0 := by decide

/-- One source qubit uses the actual three-gate positive controlled reflection. -/
@[simp] public theorem controlledElementaryGateCount_one :
    controlledElementaryGateCount 1 = 3 := by decide

/-- Two source qubits use the actual eight-gate controlled reflection. -/
@[simp] public theorem controlledElementaryGateCount_two :
    controlledElementaryGateCount 2 = 8 := by decide

/-- Three source qubits use thirteen elementary occurrences, including the controlled sign. -/
@[simp] public theorem controlledElementaryGateCount_three :
    controlledElementaryGateCount 3 = 13 := by decide

/-- Four source qubits use twenty-one elementary occurrences. -/
@[simp] public theorem controlledElementaryGateCount_four :
    controlledElementaryGateCount 4 = 21 := by decide

/-- From five source qubits onward the actual independent count has this linear formula. -/
public theorem controlledElementaryGateCount_of_five_le {width : Nat} (large : 5 ≤ width) :
    controlledElementaryGateCount width = 10 * width - 21 := by
  obtain ⟨extra, rfl⟩ : ∃ extra, width = extra + 5 := ⟨width - 5, by omega⟩
  rw [controlledElementaryGateCount, gateCount_of_five_le (by omega)]
  omega

namespace SmallPhase

theorem program_eventCost (phases width : Nat) (small : width ≤ 2) (control : Fin phases) :
    (program phases width small control).eventCost = controlledElementaryEventPool width := by
  interval_cases width
  · rfl
  · exact EncodedBit.controlledZ_eventCost _ _ _
  · exact EncodedBit.controlledTwoWireZeroReflection_eventCost _ _ _ _ _ _

theorem program_unitDepth (phases width : Nat) (small : width ≤ 2) (control : Fin phases) :
    (program phases width small control).evaluatedEventDepth (fun _ => 1) =
      controlledElementaryGateCount width := by
  interval_cases width
  · rfl
  · exact EncodedBit.controlledZ_unitDepth _ _ _
  · exact EncodedBit.controlledTwoWireZeroReflection_unitDepth _ _ _ _ _ _

end SmallPhase

namespace PhaseWorkspace

theorem program_eventCost (phases controls : Nat) (large : 2 ≤ controls)
    (control work : Fin phases) (different : control ≠ work) :
    (program phases controls control work different).eventCost =
      controlledElementaryEventPool (controls + 1) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, controls = extra + 2 := ⟨controls - 2, by omega⟩
  have actual := (layout phases (extra + 2) work).controlledZeroReflectionProgram_eventCost
    (phaseBit phases (extra + 2) control)
    (control_source_ne phases (extra + 2) control work)
    (control_output_ne phases (extra + 2) control work)
    (control_work_ne phases (extra + 2) control work different)
  change (program phases (extra + 2) control work different).eventCost = _ at actual
  rw [gatePool, if_neg (by omega), if_neg (by omega)] at actual
  exact actual

theorem program_unitDepth (phases controls : Nat) (large : 2 ≤ controls)
    (control work : Fin phases) (different : control ≠ work) :
    (program phases controls control work different).evaluatedEventDepth (fun _ => 1) =
      controlledElementaryGateCount (controls + 1) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, controls = extra + 2 := ⟨controls - 2, by omega⟩
  have actual := (layout phases (extra + 2) work).controlledZeroReflectionProgram_unitDepth
    (phaseBit phases (extra + 2) control)
    (control_source_ne phases (extra + 2) control work)
    (control_output_ne phases (extra + 2) control work)
    (control_work_ne phases (extra + 2) control work different)
  change (program phases (extra + 2) control work different).evaluatedEventDepth
    (fun _ => 1) = _ at actual
  exact actual

end PhaseWorkspace

/-- Every occurrence in the independent controlled-reflection pool is an elementary gate. -/
theorem controlledElementaryEventPool_gateCount (width : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (controlledElementaryEventPool width) =
      controlledElementaryGateCount width := by
  match width with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | extra + 3 =>
      simp only [controlledElementaryEventPool, controlledElementaryGateCount,
        ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
        ResourcePool.weightedCount_singleton, mul_one]
      omega

/-- The elementary controlled reflection invokes no opaque source query. -/
theorem controlledElementaryEventPool_queryCount (width : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .quantumSubroutine _ => 1 | _ => 0) (controlledElementaryEventPool width) = 0 := by
  match width with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | extra + 3 =>
      simp only [controlledElementaryEventPool, ResourcePool.weightedCount_add,
        ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
        mul_zero, add_zero]

/-- The selected controlled synthesis has a uniform linear elementary count. -/
theorem controlledElementaryGateCount_le (width : Nat) :
    controlledElementaryGateCount width ≤ 10 * width + 3 := by
  match width with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | extra + 5 =>
      rw [controlledElementaryGateCount, gateCount_of_five_le (by omega)]
      omega

end

end QuantumAlg.ZeroReflection
