/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Program
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources

/-!
# Bounds for the actual controlled arithmetic window lists

The existing TTK lists have at most seven elementary gates per operand bit
plus two overflow gates [TTK09, qic-loglogaddition-quant.tex:285-318]. The
actual arbitrary-work control expansion uses one or four gates per original
gate [G17, paper.tex:278-293]. The bounds below count those emitted native
lists, including signed output and arbitrary Iter restoration at width zero.

These estimates belong to the current concrete window refinement of
[LYL+26, sec_EEA/sub_opt.tex:43-48,61-66]. They do not substitute the paper's
whole-algorithm asymptotic count for the actual finite selection schedule.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowResources

noncomputable section

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowProgram

/-- Each actual low or signed TTK list has this uniform bound, including empty operands. -/
theorem focusGates_length_le (length : Nat) (operation : Operation) :
    (focusGates length operation).length ≤ 7 * length + 2 := by
  have low := Addition.TTK.low_length length
  have high := Addition.TTK.overflow_length length
  have lowerOne : length - 1 ≤ length := Nat.sub_le _ _
  have lowerTwo : length - 2 ≤ length := Nat.sub_le _ _
  cases operation with
  | addLow =>
      rw [focusGates, List.length_map, low]
      omega
  | subtractLow =>
      rw [focusGates, List.length_map, Addition.TTK.subtractionGates, List.length_reverse, low]
      omega
  | addSigned =>
      rw [focusGates, high]
      split_ifs <;> omega
  | subtractSigned =>
      rw [focusGates, Addition.TTK.overflowSubtractionGates, List.length_reverse, high]
      split_ifs <;> omega

private theorem dirtyCount_le {Data : Type} {label : BinaryLabelEncoding Data}
    (gate : GateSpec label) : GateSpec.dirtyControlCount gate ≤ 4 := by
  cases gate with
  | x target => exact (show 1 ≤ 4 from by decide)
  | cnot control target separate => exact (show 1 ≤ 4 from by decide)
  | toffoli first second target controls left right => exact (show 4 ≤ 4 from by decide)

private theorem dirtyList_le {Data : Type} {label : BinaryLabelEncoding Data}
    (gates : List (GateSpec label)) :
    (gates.map GateSpec.dirtyControlCount).sum ≤ 4 * gates.length := by
  induction gates with
  | nil => simp
  | cons gate rest ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      have current := dirtyCount_le gate
      omega

/-- The original physical grouping adds no arithmetic gate to the emitted focused TTK list. -/
theorem gates_length_le {width : Nat} (window : Window width) (operation : Operation) :
    (ArithmeticWindowProgram.gates window operation).length ≤ 7 * window.length + 2 := by
  rw [ArithmeticWindowProgram.gates, List.length_map]
  exact focusGates_length_le window.length operation

/-- Count every actual dirty-control primitive, including all work-bit cleanup gates. -/
theorem controlledGates_length_le {width : Nat} (window : Window width) (operation : Operation) :
    (ArithmeticWindowControl.gates window operation).length ≤ 28 * window.length + 8 := by
  rw [ArithmeticWindowControl.gates, GateSpec.listWithDirtyControl_length]
  have expanded := dirtyList_le (ArithmeticWindowProgram.gates window operation)
  have original := gates_length_le window operation
  omega

/-- Any selected physical window fits the already allocated full work word. -/
theorem window_length_le {width : Nat} (window : Window width) : window.length ≤ width + 3 := by
  have complete := window.complete
  omega

/-- A uniform emitted count uses only the actual original word width. -/
theorem controlledGates_length_le_frame {width : Nat} (window : Window width)
    (operation : Operation) :
    (ArithmeticWindowControl.gates window operation).length ≤ 28 * (width + 3) + 8 := by
  have actual := controlledGates_length_le window operation
  have within := window_length_le window
  omega

/-- The actual remainder trace contains exactly the actual expanded gate list. -/
theorem remainder_eventTrace_length {width : Nat} (window : Window width) (operation : Operation) :
    (ArithmeticWindowControl.program window operation).eventTrace.length =
      (ArithmeticWindowControl.gates window operation).length := by
  rw [ArithmeticWindowControl.program_eventTrace, List.length_map]

/-- Exact strict remainder depth counts the same executed list. -/
theorem remainder_unitDepth {width : Nat} (window : Window width) (operation : Operation) :
    (ArithmeticWindowControl.program window operation).evaluatedEventDepth (fun _ => 1) =
      (ArithmeticWindowControl.gates window operation).length := by
  rw [ArithmeticWindowControl.program_unitDepth, ArithmeticWindowControl.gates,
    GateSpec.listWithDirtyControl_length]

/-- Coefficient orientation preserves the literal controlled native gate count. -/
theorem coefficient_eventTrace_length {width : Nat} (window : Window width)
    (operation : Operation) :
    (CoefficientWindowProgram.controlledProgram window operation).eventTrace.length =
      (ArithmeticWindowControl.gates window operation).length := by
  rw [CoefficientWindowProgram.controlledProgram_eventTrace, List.length_map]

/-- Exact coefficient depth counts those same executed gates, with no cost-free control. -/
theorem coefficient_unitDepth {width : Nat} (window : Window width) (operation : Operation) :
    (CoefficientWindowProgram.controlledProgram window operation).evaluatedEventDepth
        (fun _ => 1) = (ArithmeticWindowControl.gates window operation).length := by
  rw [CoefficientWindowProgram.controlledProgram_unitDepth, ArithmeticWindowControl.gates,
    GateSpec.listWithDirtyControl_length]

/-- Actual remainder unit depth satisfies the independently derived full-frame envelope. -/
theorem remainder_unitDepth_le {width : Nat} (window : Window width) (operation : Operation) :
    (ArithmeticWindowControl.program window operation).evaluatedEventDepth (fun _ => 1) ≤
      28 * (width + 3) + 8 := by
  rw [remainder_unitDepth]
  exact controlledGates_length_le_frame window operation

/-- Actual coefficient unit depth satisfies the same count after its proved exact placement. -/
theorem coefficient_unitDepth_le {width : Nat} (window : Window width) (operation : Operation) :
    (CoefficientWindowProgram.controlledProgram window operation).evaluatedEventDepth
        (fun _ => 1) ≤ 28 * (width + 3) + 8 := by
  rw [coefficient_unitDepth]
  exact controlledGates_length_le_frame window operation

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowResources
