/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Reflection.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.UnitaryCircuit
import Mathlib.Tactic.IntervalCases

/-!
# Independent elementary source-reflection budgets

Widths at most three use the actual work-free constructions. Wider source
registers use the actual one-dirty construction, including both complements,
both Hadamards and the exact global-minus correction. The formulas below
contain only widths and native elementary coordinates; circuit theorems
establish their equality with the execution's own ledger and depth.
-/

namespace QuantumAlg.ZeroReflection

noncomputable section

open EncodedBit.Word.OneDirtyLayout

/-- Native elementary multiplicities of the selected minimal-work source reflection. -/
def elementaryEventPool : Nat → ResourcePool .quantum
  | 0 => 0
  | 1 => ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z"))
  | 2 =>
      2 • ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        ResourcePool.singleton (.gate (.builtin "cnot"))
  | 3 =>
      8 • ResourcePool.singleton (.gate (.builtin "x")) +
      2 • ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        ResourcePool.singleton (.gate (.builtin "toffoli"))
  | extra + 4 =>
      (2 * (extra + 4) + 2) • ResourcePool.singleton (.gate (.builtin "x")) +
      2 • ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        gateCount (extra + 3) • ResourcePool.singleton (.gate (.builtin "toffoli"))

/-- Independent total elementary count, also the sequential reflection depth. -/
public def elementaryGateCount : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | 3 => 13
  | extra + 4 => 2 * (extra + 4) + gateCount (extra + 3) + 6

namespace Small

theorem program_eventCost (width : Nat) (small : width ≤ 3) :
    (program width small).eventCost = elementaryEventPool width := by
  interval_cases width
  · rfl
  · exact EncodedBit.pauliZ_eventCost _
  · exact EncodedBit.twoWireZeroReflection_eventCost _ _ _
  · exact EncodedBit.threeWireZeroReflection_eventCost _ _ _ _ _ _

theorem program_unitDepth (width : Nat) (small : width ≤ 3) :
    (program width small).evaluatedEventDepth (fun _ => 1) = elementaryGateCount width := by
  interval_cases width
  · rfl
  · exact EncodedBit.pauliZ_unitDepth _
  · exact EncodedBit.twoWireZeroReflection_unitDepth _ _ _
  · exact EncodedBit.threeWireZeroReflection_unitDepth _ _ _ _ _ _

end Small

namespace OneDirty

theorem program_eventCost (controls : Nat) (large : 3 ≤ controls) :
    (program controls).eventCost = elementaryEventPool (controls + 1) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, controls = extra + 3 := ⟨controls - 3, by omega⟩
  have actual := (layout (extra + 3)).zeroReflectionProgram_eventCost
  change (program (extra + 3)).eventCost = _ at actual
  rw [gatePool, if_neg (by omega), if_neg (by omega)] at actual
  exact actual

theorem program_unitDepth (controls : Nat) (large : 3 ≤ controls) :
    (program controls).evaluatedEventDepth (fun _ => 1) = elementaryGateCount (controls + 1) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, controls = extra + 3 := ⟨controls - 3, by omega⟩
  have actual := (layout (extra + 3)).zeroReflectionProgram_unitDepth
  change (program (extra + 3)).evaluatedEventDepth (fun _ => 1) = _ at actual
  change _ = 2 * (extra + 4) + gateCount (extra + 3) + 6
  omega

end OneDirty

/-- No opaque subroutine coordinate occurs in the independent elementary reflection budget. -/
theorem elementaryEventPool_queryCount (width : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .quantumSubroutine _ => 1 | _ => 0) (elementaryEventPool width) = 0 := by
  match width with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | extra + 4 =>
      simp only [elementaryEventPool, ResourcePool.weightedCount_add,
        ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
        mul_zero, add_zero]

/-- Every counted occurrence belongs to the actual elementary gate family. -/
theorem elementaryEventPool_gateCount (width : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (elementaryEventPool width) = elementaryGateCount width := by
  match width with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | extra + 4 =>
      simp only [elementaryEventPool, elementaryGateCount, ResourcePool.weightedCount_add,
        ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton, mul_one]
      omega

/-- The selected elementary source synthesis has a uniform linear gate bound. -/
theorem elementaryGateCount_le (width : Nat) : elementaryGateCount width ≤ 10 * width + 9 := by
  match width with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | extra + 4 =>
      by_cases first : extra = 0
      · subst extra
        decide
      · by_cases second : extra = 1
        · subst extra
          decide
        · have count := gateCount_of_five_le (by omega : 5 ≤ extra + 3)
          simp only [elementaryGateCount, count]
          omega

end

end QuantumAlg.ZeroReflection
