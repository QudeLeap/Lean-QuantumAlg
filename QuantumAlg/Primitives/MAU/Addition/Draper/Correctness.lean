/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Draper.PhaseLayer
import all QuantumAlg.Components.Encoded.Circuit

/-!
# Exact Draper addition by a compiled classical constant

The actual circuit performs the existing no-swap QFT, the literal tensor of
one-qubit constant phases, and the adjoint of that same QFT. The only quantum
register is the `n`-bit target; the constant is an unrestricted natural-valued
compilation parameter. The basis endpoint is exact addition modulo `2^n`,
including width zero, with no relative or global phase allowance
[D00, paper.tex:130,216-233,302,352-361].
-/

namespace QuantumAlg.MAU.Addition.Draper

noncomputable section

open scoped BigOperators

/-- Add a classical natural constant to a bounded word, with exact modular wraparound. -/
def additionOutput {n : Nat} (constant : Nat) (input : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨(input.val + constant) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩

/-- The independently specified output is the least nonnegative modular sum. -/
@[simp] theorem draperAdditionOutput_value (n constant : Nat) (input : Fin (2 ^ n)) :
    (additionOutput constant input).val = (input.val + constant) % 2 ^ n := rfl

private theorem fourier_root_mul_mod (n frequency value : Nat) :
    ω n ^ (frequency * value) = ω n ^ (frequency * (value % 2 ^ n)) := by
  rw [pow_mul, pow_mul]
  have hperiod : (ω n ^ frequency) ^ (2 ^ n) = 1 := by
    rw [← pow_mul, Nat.mul_comm frequency (2 ^ n), pow_mul,
      omega_pow_eq_one, one_pow]
  exact pow_eq_pow_mod value hperiod

/-- Applying the actual phase tensor multiplies each coordinate by its exact Fourier phase. -/
theorem draperPhaseLayer_applyVec (n constant : Nat)
    (state : HilbertVector (Qubits n)) (output : Fin (2 ^ n)) :
    (phaseLayer n constant).applyVec state output =
      ω n ^ ((qftReverseBits n output).val * constant) * state output := by
  change (∑ input : Fin (2 ^ n),
    (phaseLayer n constant).matrix output input * state input) = _
  simp [draperPhaseLayer_matrix, ite_mul]

private theorem noSwap_applyVec_ket (n : Nat) (input output : Fin (2 ^ n)) :
    (qftNoSwapCircuit n).applyVec
        (NormalizedVector.ket (R := Qubits n) input).vec output =
      invSqrtN n * ω n ^ ((qftReverseBits n output).val * input.val) := by
  change HilbertOperator.applyVec
    ((qftNoSwapCircuit n).matrix : HilbertOperator (Qubits n))
    (NormalizedVector.ket (R := Qubits n) input).vec output = _
  rw [HilbertOperator.applyVec_ket]
  exact qftNoSwapCircuit_matrix_apply n output input

private theorem fourier_column_shift (n constant frequency : Nat)
    (input : Fin (2 ^ n)) :
    ω n ^ (frequency * constant) * (invSqrtN n * ω n ^ (frequency * input.val)) =
      invSqrtN n * ω n ^ (frequency * (additionOutput constant input).val) := by
  calc
    ω n ^ (frequency * constant) * (invSqrtN n * ω n ^ (frequency * input.val)) =
      invSqrtN n * ω n ^ (frequency * (input.val + constant)) := by
        rw [Nat.mul_add, pow_add]
        ring
    _ = invSqrtN n * ω n ^ (frequency * (additionOutput constant input).val) := by
      rw [draperAdditionOutput_value,
        fourier_root_mul_mod n frequency (input.val + constant)]

set_option maxHeartbeats 800000 in
-- Normalized-state coercions traverse both certified recursive circuit operators.
/-- The phase tensor translates each actual no-swap Fourier column by the compiled constant. -/
theorem draperPhaseLayer_after_qft (n constant : Nat) (input : Fin (2 ^ n)) :
    (phaseLayer n constant).applyNormalized
        ((qftNoSwapCircuit n).applyNormalized (NormalizedVector.ket input)) =
      (qftNoSwapCircuit n).applyNormalized
        (NormalizedVector.ket (additionOutput constant input)) := by
  apply NormalizedVector.ext
  intro output
  change (phaseLayer n constant).applyVec
      ((qftNoSwapCircuit n).applyVec
        (NormalizedVector.ket (R := Qubits n) input).vec) output =
    (qftNoSwapCircuit n).applyVec
      (NormalizedVector.ket (R := Qubits n) (additionOutput constant input)).vec output
  rw [draperPhaseLayer_applyVec, noSwap_applyVec_ket, noSwap_applyVec_ket]
  exact fourier_column_shift n constant (qftReverseBits n output).val input

/-- Actual QFT, phase tensor, and inverse QFT on the same target register. -/
def additionProgram (n constant : Nat) : UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.seq (qftNoSwapCircuit n)
    (UnitaryCircuit.seq (phaseLayer n constant) (qftNoSwapCircuit n).dagger)

/-- The real compiled circuit adds the constant exactly at every word width. -/
theorem draperAddition_apply_ket (n constant : Nat) (input : Fin (2 ^ n)) :
    (additionProgram n constant).applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket (additionOutput constant input) := by
  rw [additionProgram, UnitaryCircuit.applyNormalized_seq,
    UnitaryCircuit.applyNormalized_seq, draperPhaseLayer_after_qft]
  exact UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
    (qftNoSwapCircuit n) (NormalizedVector.ket (additionOutput constant input))

/-- Exact encoded addition uses only the target word and the literal QFT/phase sequence. -/
theorem draperAddition_realizes (n constant : Nat) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.finIdentity n)
      (additionProgram n constant) (additionOutput constant) where
  apply_encoded_ket := by
    intro input
    exact draperAddition_apply_ket n constant input

end

end QuantumAlg.MAU.Addition.Draper
