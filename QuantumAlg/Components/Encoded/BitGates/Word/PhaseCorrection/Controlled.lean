/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.PhaseCorrection
import all QuantumAlg.Components.Encoded.BitGates.Small.Phase
import all QuantumAlg.Components.Encoded.BitGates.Reflection.Resources
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual coherent control of a selected Pauli correction

Each selected word position executes the existing H-CNOT-H controlled Z.
The zero-control branch flips the supplied control before the complete word
and restores it afterwards, charging both native X gates. The same complete
physical layout is retained, with no additional wire or initial-state premise.
Full encoded columns and arbitrary reference coordinates retain the exact
relative phase in both control sectors.
-/

namespace QuantumAlg.EncodedBit.Word.PhaseCorrection.Controlled

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)
variable {environment : oracles.Interpretation}
variable (control : EncodedBit encoding) (word : EncodedBit.Word encoding width)
  (different : ∀ index, control.wire ≠ (word.bit index).wire)

/-- Positive coherent control uses one actual H-CNOT-H sequence per selected position. -/
def positiveSequence : List (Fin width) →
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum
  | [] => .identity AlgorithmGate.model oracles physical.toQuantum
  | index :: rest =>
      (control.controlledZ physical oracles (word.bit index) (different index)).seq
        (positiveSequence rest)

/-- Both control sectors retain every input coordinate and the exact selected sign. -/
lemma controlledPhaseCorrection_positive_ket (indices : List (Fin width)) (state : Data) :
    ((positiveSequence physical oracles control word different indices).applyVec environment)
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      (if control.get state then sign word state indices else 1) •
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  induction indices with
  | nil =>
      simp only [positiveSequence, UnitaryCircuit.applyVec, UnitaryCircuit.identity_matrix,
        UnitaryOperator.one_applyVec, sign, ite_self, one_smul]
  | cons index rest ih =>
      rw [positiveSequence, UnitaryCircuit.applyVec_seq, controlledZ_applyVec_encoded_ket,
        UnitaryCircuit.applyVec_smul, ih, smul_smul]
      cases control.get state <;> cases value : (word.bit index).get state <;>
        simp [value, sign]

include different in
private lemma sign_control_flip (indices : List (Fin width)) (state : Data) :
    sign word (control.flip state) indices = sign word state indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [sign, get_flip_of_wire_ne control (word.bit index) (different index), ih]
      rfl

private lemma controlX_ket (state : Data) :
    (((GateSpec.x control).program physical oracles).applyVec environment)
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode (control.flip state)))).vec :=
  congrArg NormalizedVector.vec
    ((GateSpec.realizes physical oracles (.x control) environment).apply_encoded_ket state)

/-- Select a coherent sector using the supplied control and, for zero, two actual X gates. -/
def sequence (active : Bool) (indices : List (Fin width)) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  if active then positiveSequence physical oracles control word different indices else
    (((GateSpec.x control).program physical oracles).seq
      (positiveSequence physical oracles control word different indices)).seq
        ((GateSpec.x control).program physical oracles)

/-- The full original label returns with precisely the phase of the selected control sector. -/
lemma controlledPhaseCorrection_sequence_ket (active : Bool)
    (indices : List (Fin width)) (state : Data) :
    ((sequence physical oracles control word different active indices).applyVec environment)
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      (if control.get state = active then sign word state indices else 1) •
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  cases active with
  | true =>
      exact controlledPhaseCorrection_positive_ket physical oracles
        control word different indices state
  | false =>
      simp only [sequence, Bool.false_eq_true, if_false, UnitaryCircuit.applyVec_seq]
      rw [controlX_ket, controlledPhaseCorrection_positive_ket,
        UnitaryCircuit.applyVec_smul, controlX_ket, get_flip_self,
        sign_control_flip control word different, flip_flip]
      cases control.get state <;> rfl

/-- The same phase cancels exactly, including coherences between the two control sectors. -/
lemma controlledPhaseCorrection_cancel_ket (active : Bool)
    (indices : List (Fin width)) (state : Data) :
    ((sequence physical oracles control word different active indices).applyVec environment)
        ((if control.get state = active then sign word state indices else 1) •
          (NormalizedVector.ket (R := physical.toQuantum.register)
            (physical.basisEquiv.symm (encoding.encode state))).vec) =
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode state))).vec := by
  rw [UnitaryCircuit.applyVec_smul, controlledPhaseCorrection_sequence_ket, smul_smul]
  split_ifs
  · rw [phaseCorrection_sign_square, one_smul]
  · simp only [mul_one, one_smul]

/-- Every complete reference column retains the selected phase and all original coordinates. -/
lemma controlledPhaseCorrection_reference_entry (active : Bool)
    (indices : List (Fin width)) (state : Data) {Reference : Register}
    (row : physical.toQuantum.register.Index) (left right : Reference.Index) :
    UnitaryOperator.prodTensor
        ((sequence physical oracles control word different active indices).matrix environment)
        (1 : UnitaryOperator Reference) (row, left)
        (physical.basisEquiv.symm (encoding.encode state), right) =
      if row = physical.basisEquiv.symm (encoding.encode state) ∧ left = right then
        (if control.get state = active then sign word state indices else 1) else 0 := by
  have column := congrArg
    (fun vector : HilbertVector physical.toQuantum.register => vector row)
    (controlledPhaseCorrection_sequence_ket (environment := environment)
      physical oracles control word different
      active indices state)
  have matrixColumn := (HilbertOperator.applyVec_ket
    (((sequence physical oracles control word different active indices).matrix environment) :
      HilbertOperator physical.toQuantum.register)
    (physical.basisEquiv.symm (encoding.encode state)) row).symm.trans column
  rw [UnitaryOperator.prodTensor_apply, matrixColumn]
  simp only [PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply]
  change ((if control.get state = active then sign word state indices else 1) *
    (if row = physical.basisEquiv.symm (encoding.encode state) then 1 else 0)) *
    (if left = right then 1 else 0) = _
  by_cases selected : row = physical.basisEquiv.symm (encoding.encode state) <;>
    by_cases reference : left = right <;> simp [selected, reference]

/-- The positive word's ordered trace records each literal H, CNOT, H occurrence. -/
lemma controlledPhaseCorrection_positive_trace (indices : List (Fin width)) :
    (positiveSequence physical oracles control word different indices).eventTrace =
      indices.flatMap (fun _ => [.gate .singleQubit, .gate .cnot, .gate .singleQubit]) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [positiveSequence, UnitaryCircuit.seq_eventTrace, controlledZ,
        conjugateHadamard_eventTrace, GateSpec.program_eventTrace, ih]
      rfl

/-- The zero-control trace also retains the two actual control flips in execution order. -/
lemma controlledPhaseCorrection_sequence_trace (active : Bool) (indices : List (Fin width)) :
    (sequence physical oracles control word different active indices).eventTrace =
      if active then
        indices.flatMap (fun _ => [.gate .singleQubit, .gate .cnot, .gate .singleQubit])
      else [.gate .singleQubit] ++
        indices.flatMap (fun _ => [.gate .singleQubit, .gate .cnot, .gate .singleQubit]) ++
          [.gate .singleQubit] := by
  cases active <;>
    simp only [sequence, Bool.false_eq_true, if_false, if_true, UnitaryCircuit.seq_eventTrace,
      GateSpec.program_eventTrace, controlledPhaseCorrection_positive_trace]
  all_goals rfl

/-- Native multiplicities charge two Hadamards and one CNOT per selected position. -/
lemma controlledPhaseCorrection_positive_cost (indices : List (Fin width)) :
    (positiveSequence physical oracles control word different indices).eventCost =
      indices.length •
        (2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
          (.gate .singleQubit) +
          ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
            (.gate .cnot)) := by
  induction indices with
  | nil => exact (zero_nsmul _).symm
  | cons index rest ih =>
      rw [positiveSequence, UnitaryCircuit.seq_eventCost, controlledZ_eventCost, ih,
        List.length_cons, succ_nsmul]
      exact add_comm _ _

/-- The complete resource pool counts all selected gates and both negative-control X gates. -/
lemma controlledPhaseCorrection_sequence_cost (active : Bool) (indices : List (Fin width)) :
    (sequence physical oracles control word different active indices).eventCost =
      indices.length •
        (2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
          (.gate .singleQubit) +
          ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
            (.gate .cnot)) +
        (if active then 0 else
          2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
            (.gate .singleQubit)) := by
  cases active <;>
    simp only [sequence, Bool.false_eq_true, if_false, if_true, UnitaryCircuit.seq_eventCost,
      GateSpec.program_eventCost, controlledPhaseCorrection_positive_cost, add_zero]
  change (ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
    (.gate .singleQubit) + _) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) = _
  rw [two_nsmul]
  abel

/-- Serial depth is exactly three native durations per selected correction. -/
lemma controlledPhaseCorrection_positive_depth (indices : List (Fin width)) :
    (positiveSequence physical oracles control word different indices).evaluatedEventDepth
      (fun _ => 1) = 3 * indices.length := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [positiveSequence, UnitaryCircuit.evaluatedEventDepth_seq, controlledZ_unitDepth, ih,
        List.length_cons]
      omega

/-- Both control flips remain in the complete serial depth of the zero-control word. -/
lemma controlledPhaseCorrection_sequence_depth (active : Bool) (indices : List (Fin width)) :
    (sequence physical oracles control word different active indices).evaluatedEventDepth
      (fun _ => 1) = 3 * indices.length + (if active then 0 else 2) := by
  cases active <;>
    simp only [sequence, Bool.false_eq_true, if_false, if_true,
      UnitaryCircuit.evaluatedEventDepth_seq, GateSpec.program_unitDepth,
      controlledPhaseCorrection_positive_depth]
  all_goals omega

/-- The actual stored measurement mask selects exactly its original one-bit positions. -/
def program (active : Bool) (outcome : Fin width → Bool) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  sequence physical oracles control word different active (selected outcome)

/-- The same selected width bounds the actual phase word without changing any endpoint budget. -/
lemma controlledPhaseCorrection_program_depth_bound (active : Bool)
    (outcome : Fin width → Bool) :
    (program physical oracles control word different active outcome).evaluatedEventDepth
      (fun _ => 1) ≤ 3 * width + (if active then 0 else 2) := by
  rw [program, controlledPhaseCorrection_sequence_depth]
  have selectedBound := phaseCorrection_selected_count_le outcome
  omega

end

end QuantumAlg.EncodedBit.Word.PhaseCorrection.Controlled
