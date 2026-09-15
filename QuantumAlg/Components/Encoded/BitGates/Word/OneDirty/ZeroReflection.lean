/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Phase
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Complement
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.PauliZ
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.Circuit

/-!
# Elementary reflection through a zero word with arbitrary restored work

Complementing every reflected wire converts its all-zero condition into the
all-one phase condition. The reverse complement restores the complete input
label. Four actual X/Z gates supply the final global minus, giving the exact
positive reflection `2|0><0| - I` rather than its negative. The work bit is
arbitrary throughout and remains unchanged as part of the complete label.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}
variable (layout : OneDirtyLayout (encoding := encoding) controls)

/-- All reflected positions, starting at the phase target, then the original controls. -/
def reflectionWord : Word encoding (controls + 1) :=
  ⟨Fin.cases layout.output layout.source.bit⟩

/-- Every reflected coordinate is a distinct original physical wire. -/
theorem reflectionWord_injective :
    Function.Injective (fun index => (layout.reflectionWord.bit index).wire) := by
  intro left right
  refine Fin.cases ?_ (fun left => ?_) left
  · refine Fin.cases ?_ (fun right => ?_) right
    · intro _
      rfl
    · intro same
      exact False.elim ((layout.source_output_ne right) same.symm)
  · refine Fin.cases ?_ (fun right => ?_) right
    · intro same
      exact False.elim ((layout.source_output_ne left) same)
    · intro same
      exact congrArg Fin.succ (layout.source_injective same)

/-- The independent zero predicate reads all reflected bits and excludes the work wire. -/
def reflectedZero (state : Data) : Prop :=
  (∀ index, (layout.source.bit index).get state = false) ∧ layout.output.get state = false

instance reflectedZero_decidable (state : Data) : Decidable (layout.reflectedZero state) := by
  unfold reflectedZero
  infer_instance

private theorem complemented_source (state : Data) (index : Fin controls) :
    (layout.source.bit index).get
        (GateSpec.stepList layout.reflectionWord.complementGates state) =
      !(layout.source.bit index).get state :=
  layout.reflectionWord.complementGates_get layout.reflectionWord_injective state index.succ

private theorem complemented_output (state : Data) :
    layout.output.get (GateSpec.stepList layout.reflectionWord.complementGates state) =
      !layout.output.get state :=
  layout.reflectionWord.complementGates_get layout.reflectionWord_injective state 0

private theorem complemented_condition (state : Data) :
    ((∀ index, (layout.source.bit index).get
        (GateSpec.stepList layout.reflectionWord.complementGates state) = true) ∧
      layout.output.get (GateSpec.stepList layout.reflectionWord.complementGates state) = true) ↔
        layout.reflectedZero state := by
  have notTrue (value : Bool) : (Bool.not value = true) ↔ value = false := by
    cases value <;> decide
  simp only [complemented_source, complemented_output, notTrue, reflectedZero]

private theorem list_applyVec (gates : List (GateSpec encoding)) (state : Data) :
    (GateSpec.programList gates).applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      (NormalizedVector.ket (R := Qubits encoding.width)
        (encoding.encode (GateSpec.stepList gates state))).vec :=
  congrArg NormalizedVector.vec ((GateSpec.realizesList gates).apply_encoded_ket state)

/-- Negative zero phase, with the full complement/uncomplement sequence retained. -/
def negativeZeroPhase : UnitaryCircuit (Qubits encoding.width) :=
  ((GateSpec.programList layout.reflectionWord.complementGates).seq layout.phaseProgram).seq
    (GateSpec.programList layout.reflectionWord.complementGates.reverse)

/-- The negative zero phase restores the entire label, including arbitrary dirty work. -/
theorem negativeZeroPhase_applyVec_encoded_ket (state : Data) :
    layout.negativeZeroPhase.applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      (if layout.reflectedZero state then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  simp only [negativeZeroPhase, UnitaryCircuit.applyVec_seq]
  rw [list_applyVec, phaseProgram_applyVec_encoded_ket]
  simp only [complemented_condition]
  by_cases zeroWord : layout.reflectedZero state
  · rw [if_pos zeroWord, if_pos zeroWord]
    rw [← neg_one_smul ℂ
      (NormalizedVector.ket (R := Qubits encoding.width)
        (encoding.encode (GateSpec.stepList layout.reflectionWord.complementGates state))).vec]
    rw [UnitaryCircuit.applyVec_smul, list_applyVec, complementGates_reverse_restore]
  · rw [if_neg zeroWord, if_neg zeroWord, list_applyVec, complementGates_reverse_restore,
      one_smul]

/-- The exact positive zero reflection includes its physical global-minus correction. -/
def zeroReflectionProgram : UnitaryCircuit (Qubits encoding.width) :=
  layout.negativeZeroPhase.seq layout.output.globalMinus

/-- Exact positive zero reflection on the complete encoded input, with no work-state premise. -/
theorem zeroReflectionProgram_applyVec_encoded_ket (state : Data) :
    layout.zeroReflectionProgram.applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      if layout.reflectedZero state then
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec
      else -(NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  rw [zeroReflectionProgram, UnitaryCircuit.applyVec_seq,
    negativeZeroPhase_applyVec_encoded_ket, UnitaryCircuit.applyVec_smul,
    globalMinus_applyVec_encoded_ket]
  by_cases zeroWord : layout.reflectedZero state <;> simp [zeroWord]

/-- Every complement gate, phase gate, and global-minus gate is charged in this sequence. -/
theorem zeroReflectionProgram_eventTrace_length :
    layout.zeroReflectionProgram.eventTrace.length =
      2 * (controls + 1) + layout.gates.length + 6 := by
  simp only [zeroReflectionProgram, negativeZeroPhase, UnitaryCircuit.seq_eventTrace,
    List.length_append, GateSpec.programList_eventTrace, List.length_map,
    List.length_reverse, complementGates_length, phaseProgram_eventTrace_length,
    globalMinus_eventTrace_length]
  omega

/-- The exact positive reflection retains a linear actual elementary gate bound. -/
theorem zeroReflectionProgram_eventTrace_length_le :
    layout.zeroReflectionProgram.eventTrace.length ≤ 10 * controls + 9 := by
  rw [zeroReflectionProgram_eventTrace_length]
  have actual := layout.gates_length_le
  omega

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
