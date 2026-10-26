/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical.Labels
import all QuantumAlg.Components.Encoded.BitGates.Hadamard
import all QuantumAlg.Components.Encoded.BitGates.PauliZ
import all QuantumAlg.Components.Gates.PhaseOperator

/-!
# Actual native control gates on the complete canonical arithmetic labels

Only the original control changes under its native H or X. Both original
arithmetic words and all three helper systems retain their physical values.
The full ket equations preserve their exact native phases
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical

noncomputable section

open NormalizedVector

/-- The actual native control flip retains the source and all three physically zero helpers. -/
lemma cleanLabel_control_flip (width : Nat) (control : Bool) (source : BitVec width) :
    (layout width).control.flip (cleanLabel width control source) =
      cleanLabel width (!control) source := by
  apply label_ext width
  intro port
  by_cases selected : port = .inl ()
  · subst port
    change (layout width).control.get
      ((layout width).control.flip (cleanLabel width control source)) =
      (layout width).control.get (cleanLabel width (!control) source)
    rw [EncodedBit.get_flip_self, cleanLabel_control, cleanLabel_control]
  · have different : (layout width).control.wire ≠ ((layout width).bit port).wire :=
      (layout width).wire_ne (fun equal => selected equal.symm)
    rw [EncodedBit.get_flip_of_wire_ne _ _ different]
    simp only [cleanLabel, label_bit]
    rcases port with singleton | rest
    · cases singleton
      exact False.elim (selected rfl)
    · cases rest <;> rfl

/-- Exact H action on each complete physical input, including the input-one sign. -/
lemma cleanLabel_hadamard (width : Nat) (control : Bool) (source : BitVec width)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((layout width).control.hadamard (qubits width) oracles).applyVec environment
      (NormalizedVector.ket (R := (qubits width).toQuantum.register)
        ((qubits width).basisEquiv.symm (cleanLabel width control source))).vec =
      invSqrt2 • ((if control then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := (qubits width).toQuantum.register)
          ((qubits width).basisEquiv.symm (cleanLabel width control source))).vec +
        (NormalizedVector.ket (R := (qubits width).toQuantum.register)
          ((qubits width).basisEquiv.symm (cleanLabel width (!control) source))).vec) := by
  have actual := EncodedBit.hadamard_applyVec_encoded_ket (layout width).control (qubits width)
    oracles (environment := environment) (cleanLabel width control source)
  rw [cleanLabel_control, cleanLabel_control_flip] at actual
  exact actual

/-- Exact native Z action preserves all original source/helper values and its coherent sign. -/
lemma cleanLabel_pauliZ (width : Nat) (control : Bool) (source : BitVec width)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((layout width).control.pauliZ (qubits width) oracles).applyVec environment
      (NormalizedVector.ket (R := (qubits width).toQuantum.register)
        ((qubits width).basisEquiv.symm (cleanLabel width control source))).vec =
      (if control then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := (qubits width).toQuantum.register)
          ((qubits width).basisEquiv.symm (cleanLabel width control source))).vec := by
  have actual := EncodedBit.pauliZ_applyVec_encoded_ket (layout width).control (qubits width)
    oracles (environment := environment) (cleanLabel width control source)
  rw [cleanLabel_control] at actual
  exact actual

private lemma phase_entry (angle : Real) (row column : Fin 2) :
    phaseGateOp angle row column =
      if row = column then (if column = 0 then 1 else
        Complex.exp ((angle : Complex) * Complex.I)) else 0 := by
  rw [phaseGateOp_diagonal]
  by_cases same : row = column
  · subst row
    simp
  · simp [same]

/-- Any actual stored-feedback phase preserves the complete physical label with its exact phase. -/
lemma cleanLabel_phase (width : Nat) (control : Bool) (source : BitVec width) (angle : Real)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    (Gate.singleQubitAt (qubits width).toQuantum oracles (phaseGateOp angle)
      (layout width).control.wire rfl).applyVec environment
      (NormalizedVector.ket (R := (qubits width).toQuantum.register)
        ((qubits width).basisEquiv.symm (cleanLabel width control source))).vec =
      (if control then Complex.exp ((angle : Complex) * Complex.I) else 1) •
        (NormalizedVector.ket (R := (qubits width).toQuantum.register)
          ((qubits width).basisEquiv.symm (cleanLabel width control source))).vec := by
  have actual := Gate.singleQubitAt_diagonal_applyVec_ket (qubits width) oracles
    (environment := environment) (phaseGateOp angle)
    (fun value => if value = 0 then 1 else Complex.exp ((angle : Complex) * Complex.I))
    (phase_entry angle) (layout width).control.wire
    ((qubits width).basisEquiv.symm (cleanLabel width control source))
  have read : (qubits width).basisEquiv.symm (cleanLabel width control source)
      (layout width).control.wire = finTwoEquiv.symm control := by
    have original := (layout width).control.targetBasisEquiv_first (cleanLabel width control source)
    rw [cleanLabel_control] at original
    exact original
  rw [read] at actual
  have scalar : (if finTwoEquiv.symm control = 0 then (1 : ℂ) else
      Complex.exp ((angle : Complex) * Complex.I)) =
      if control then Complex.exp ((angle : Complex) * Complex.I) else 1 := by
    cases control <;> rfl
  rw [scalar] at actual
  unfold UnitaryCircuit.applyVec
  exact actual

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical
