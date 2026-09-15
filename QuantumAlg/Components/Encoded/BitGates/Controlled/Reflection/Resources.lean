/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Reflection.Resources
import all QuantumAlg.Components.Encoded.BitGates.Small.ControlledZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.ControlledZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources

/-!
# Exact elementary resources of the controlled source reflection

The external control is a real additional control of the same elementary
multi-control construction. Its final Z supplies the exact controlled global
minus. The ledger and sequential depth below count these actual gates;
there is no higher-order controlled gate coordinate in this synthesis.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

theorem controlledTwoWireZeroReflection_eventCost (control first second : EncodedBit encoding)
    (controlFirst : control.wire ≠ first.wire)
    (controlSecond : control.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) :
    (control.controlledTwoWireZeroReflection first second controlFirst controlSecond
      firstSecond).eventCost =
      4 • ResourcePool.singleton (.gate (.builtin "x")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) +
      ResourcePool.singleton (.gate (.builtin "toffoli")) +
      ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) := by
  rw [controlledTwoWireZeroReflection, UnitaryCircuit.seq_eventCost, pauliZ_eventCost,
    GateSpec.conjugateProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost]
  have reversed : ([GateSpec.x first, .x second] : List (GateSpec encoding)).reverse =
      [.x second, .x first] := rfl
  rw [reversed]
  simp only [GateSpec.programList_eventCost, List.map_cons, List.map_nil, GateSpec.event,
    ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, doubleControlledZ_eventCost]
  apply Multiset.ext.mpr
  intro event
  simp only [Multiset.count_add, Multiset.count_nsmul]
  ring

theorem controlledTwoWireZeroReflection_unitDepth (control first second : EncodedBit encoding)
    (controlFirst : control.wire ≠ first.wire)
    (controlSecond : control.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) :
    (control.controlledTwoWireZeroReflection first second controlFirst controlSecond
      firstSecond).evaluatedEventDepth (fun _ => 1) = 8 := by
  simp only [controlledTwoWireZeroReflection, UnitaryCircuit.evaluatedEventDepth_seq,
    GateSpec.conjugateProgram_unitDepth, List.length_cons, List.length_nil,
    doubleControlledZ_unitDepth, pauliZ_unitDepth]

namespace Word.OneDirtyLayout

variable {controls : Nat} (layout : OneDirtyLayout (encoding := encoding) controls)
variable (control : EncodedBit encoding)
variable (sourceNe : ∀ index, control.wire ≠ (layout.source.bit index).wire)
variable (outputNe : control.wire ≠ layout.output.wire)
variable (workNe : control.wire ≠ layout.work.wire)

/-- Complement only the reflected source, and charge the final Z on the actual control. -/
theorem controlledZeroReflectionProgram_eventCost :
    (layout.controlledZeroReflectionProgram control sourceNe outputNe workNe).eventCost =
      (2 * (controls + 1)) • ResourcePool.singleton (.gate (.builtin "x")) +
      2 • ResourcePool.singleton (.gate (.builtin "hadamard")) + gatePool (controls + 1) +
      ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "pauli-z")) := by
  simp only [controlledZeroReflectionProgram, controlledNegativeZeroPhase,
    UnitaryCircuit.seq_eventCost, complementGates_eventCost, complementGates_reverse_eventCost,
    phaseProgram_eventCost, pauliZ_eventCost]
  apply Multiset.ext.mpr
  intro event
  simp only [Multiset.count_add, Multiset.count_nsmul]
  ring

/-- The controlled elementary sequence has exactly its independently counted gate depth. -/
theorem controlledZeroReflectionProgram_unitDepth :
    (layout.controlledZeroReflectionProgram control sourceNe outputNe workNe).evaluatedEventDepth
      (fun _ => 1) = 2 * (controls + 1) + gateCount (controls + 1) + 3 := by
  simp only [controlledZeroReflectionProgram, controlledNegativeZeroPhase,
    UnitaryCircuit.evaluatedEventDepth_seq, GateSpec.programList_evaluatedEventDepth_unit,
    List.length_reverse, complementGates_length, phaseProgram_unitDepth, pauliZ_unitDepth]
  omega

end Word.OneDirtyLayout

end

end QuantumAlg.EncodedBit
