/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Phase
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Complement
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.PauliZ
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector

/-!
# Source-correct controlled zero reflection from elementary gates

The external control joins the actual MCX control set; the reflected word
alone receives the complement and inverse complement. A final Pauli Z on
the external control supplies the exact controlled global minus. Thus no
high-order controlled-Toffoli declaration is treated as an elementary gate,
and control zero is exactly identity on the whole encoded state.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}
variable (layout : OneDirtyLayout (encoding := encoding) controls)
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)
variable (control : EncodedBit encoding)
variable (sourceNe : ∀ index, control.wire ≠ (layout.source.bit index).wire)
variable (outputNe : control.wire ≠ layout.output.wire)
variable (workNe : control.wire ≠ layout.work.wire)

/-- Add the actual positive control while retaining the same arbitrary work bit. -/
def withControl : OneDirtyLayout (encoding := encoding) (controls + 1) where
  source := ⟨Fin.cases control layout.source.bit⟩
  output := layout.output
  work := layout.work
  source_injective := by
    intro left right
    refine Fin.cases ?_ (fun left => ?_) left
    · refine Fin.cases ?_ (fun right => ?_) right
      · intro _
        rfl
      · intro same
        exact False.elim (sourceNe right same)
    · refine Fin.cases ?_ (fun right => ?_) right
      · intro same
        exact False.elim (sourceNe left same.symm)
      · intro same
        exact congrArg Fin.succ (layout.source_injective same)
  source_output_ne := Fin.cases outputNe layout.source_output_ne
  source_work_ne := Fin.cases workNe layout.source_work_ne
  work_output_ne := layout.work_output_ne

include sourceNe outputNe in
private theorem control_complemented_get (state : Data) :
    control.get (GateSpec.stepList layout.reflectionWord.complementGates state) =
      control.get state := by
  apply layout.reflectionWord.complementGates_get_other control
  intro index
  refine Fin.cases ?_ (fun index => ?_) index
  · exact outputNe.symm
  · exact (sourceNe index).symm

private theorem controlled_complemented_condition (state : Data) :
    ((∀ index, ((layout.withControl control sourceNe outputNe workNe).source.bit index).get
        (GateSpec.stepList layout.reflectionWord.complementGates state) = true) ∧
      layout.output.get (GateSpec.stepList layout.reflectionWord.complementGates state) = true) ↔
        control.get state = true ∧ layout.reflectedZero state := by
  have headAndTail (state : Data) :
      (∀ index, ((layout.withControl control sourceNe outputNe workNe).source.bit index).get
        state = true) ↔
        control.get state = true ∧ ∀ index, (layout.source.bit index).get state = true := by
    constructor
    · intro allBits
      exact ⟨allBits 0, fun index => allBits index.succ⟩
    · rintro ⟨head, tail⟩ index
      exact Fin.cases head tail index
  have outputGet := layout.reflectionWord.complementGates_get
    layout.reflectionWord_injective state 0
  have sourceGet (index : Fin controls) :
      (layout.source.bit index).get
          (GateSpec.stepList layout.reflectionWord.complementGates state) =
        !(layout.source.bit index).get state :=
    layout.reflectionWord.complementGates_get layout.reflectionWord_injective state index.succ
  change layout.output.get (GateSpec.stepList layout.reflectionWord.complementGates state) =
    !layout.output.get state at outputGet
  have notTrue (value : Bool) : (Bool.not value = true) ↔ value = false := by
    cases value <;> decide
  rw [headAndTail, control_complemented_get layout control sourceNe outputNe]
  simp only [sourceGet, outputGet, notTrue, reflectedZero, and_assoc]

private theorem list_applyVec (gates : List (GateSpec encoding)) (state : Data) :
    (GateSpec.programList physical oracles gates).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode (GateSpec.stepList gates state)))).vec :=
  congrArg NormalizedVector.vec
    ((GateSpec.realizesList physical oracles gates).apply_encoded_ket state)

/-- Controlled negative zero phase, without complementing the external positive control. -/
def controlledNegativeZeroPhase : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  ((GateSpec.programList physical oracles layout.reflectionWord.complementGates).seq
    ((layout.withControl control sourceNe outputNe workNe).phaseProgram physical oracles)).seq
      (GateSpec.programList physical oracles layout.reflectionWord.complementGates.reverse)

private theorem controlledNegativeZeroPhase_applyVec (state : Data) :
    (layout.controlledNegativeZeroPhase physical oracles control sourceNe outputNe workNe).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      (if control.get state = true ∧ layout.reflectedZero state then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  simp only [controlledNegativeZeroPhase, UnitaryCircuit.applyVec_seq]
  rw [list_applyVec, phaseProgram_applyVec_encoded_ket]
  change (GateSpec.programList physical oracles
    layout.reflectionWord.complementGates.reverse).applyVec
    (if (∀ index,
        ((layout.withControl control sourceNe outputNe workNe).source.bit index).get
          (GateSpec.stepList layout.reflectionWord.complementGates state) = true) ∧
        layout.output.get (GateSpec.stepList layout.reflectionWord.complementGates state) = true
      then -(NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm
          (encoding.encode (GateSpec.stepList layout.reflectionWord.complementGates state)))).vec
      else (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm
          (encoding.encode
            (GateSpec.stepList layout.reflectionWord.complementGates state)))).vec) = _
  simp only [controlled_complemented_condition]
  by_cases active : control.get state = true ∧ layout.reflectedZero state
  · rw [if_pos active, if_pos active]
    rw [← neg_one_smul ℂ
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm
          (encoding.encode (GateSpec.stepList layout.reflectionWord.complementGates state)))).vec]
    rw [UnitaryCircuit.applyVec_smul, list_applyVec, complementGates_reverse_restore]
  · rw [if_neg active, if_neg active, list_applyVec, complementGates_reverse_restore, one_smul]

/-- Positive source reflection: its controlled global minus is one actual Pauli Z. -/
def controlledZeroReflectionProgram :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (layout.controlledNegativeZeroPhase physical oracles control sourceNe outputNe workNe).seq
    (control.pauliZ physical oracles)

/-- Control zero is exact identity; control one has precisely the source's positive zero phase. -/
theorem controlledZeroReflectionProgram_applyVec_encoded_ket (state : Data) :
    (layout.controlledZeroReflectionProgram physical oracles control
      sourceNe outputNe workNe).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      if control.get state then
        if layout.reflectedZero state then
          (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec
        else -(NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec
      else (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  rw [controlledZeroReflectionProgram, UnitaryCircuit.applyVec_seq,
    controlledNegativeZeroPhase_applyVec, UnitaryCircuit.applyVec_smul,
    pauliZ_applyVec_encoded_ket]
  by_cases zeroWord : layout.reflectedZero state <;> cases control.get state <;> simp [zeroWord]

/-- The literal controlled source reflection charges all actual gates, including its final Z. -/
theorem controlledZeroReflectionProgram_eventTrace_length :
    (layout.controlledZeroReflectionProgram physical oracles control
      sourceNe outputNe workNe).eventTrace.length =
      2 * (controls + 1) + (layout.withControl control sourceNe outputNe workNe).gates.length +
        3 := by
  simp only [controlledZeroReflectionProgram, controlledNegativeZeroPhase,
    UnitaryCircuit.seq_eventTrace, List.length_append, GateSpec.programList_eventTrace,
    List.length_map, List.length_reverse, complementGates_length,
    phaseProgram_eventTrace_length, pauliZ_eventTrace, List.length_singleton]
  omega

/-- Adding the positive control keeps the actual elementary event count linear. -/
theorem controlledZeroReflectionProgram_eventTrace_length_le :
    (layout.controlledZeroReflectionProgram physical oracles control
      sourceNe outputNe workNe).eventTrace.length ≤
      10 * (controls + 1) + 4 := by
  rw [controlledZeroReflectionProgram_eventTrace_length]
  have actual := (layout.withControl control sourceNe outputNe workNe).gates_length_le
  omega

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
