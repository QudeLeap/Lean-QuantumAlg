/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.PauliZ
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Literal Pauli correction selected by a classical word

The selected positions execute the existing addressed Pauli-Z gates. On each
complete encoded basis label their exact sign is the product of the selected
bit signs. Applying that sign a second time cancels it exactly, including
relative phases between different basis inputs. The program retains the
whole original physical register and allocates no systems.

This is the unitary correction used after recomputing a measured arithmetic
word [LYL+26, sec_point_add/sec_point_add.tex:85-105]. Reading the actual
measurement record and the surrounding recomputation are separate circuit
composition obligations; the word below specifies an individual branch.
-/

namespace QuantumAlg.EncodedBit.Word.PhaseCorrection

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Existing Z gates at the selected positions, with the full physical register retained. -/
def sequence (word : EncodedBit.Word encoding width) :
    List (Fin width) → UnitaryCircuit (Qubits encoding.width)
  | [] => .identity (Qubits encoding.width) (List.range encoding.width) List.nodup_range
  | index :: rest => .seq (word.bit index).pauliZ (sequence word rest)

/-- Exact scalar contributed by the selected bit phases. -/
def sign (word : EncodedBit.Word encoding width) (state : Data) : List (Fin width) → ℂ
  | [] => 1
  | index :: rest => (if (word.bit index).get state then -1 else 1) * sign word state rest

/-- The full encoded input is unchanged, with its exact selected parity sign retained. -/
theorem phaseCorrection_sequence_ket (word : EncodedBit.Word encoding width)
    (indices : List (Fin width)) (state : Data) :
    (sequence word indices).applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      sign word state indices •
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  induction indices with
  | nil => simp only [sequence, UnitaryCircuit.applyVec_identity, sign, one_smul]
  | cons index rest induction =>
      rw [sequence, UnitaryCircuit.applyVec_seq, pauliZ_applyVec_encoded_ket,
        UnitaryCircuit.applyVec_smul, induction, smul_smul]
      rfl

/-- Every selected phase squares to one; no global or relative sign is discarded. -/
theorem phaseCorrection_sign_square (word : EncodedBit.Word encoding width)
    (state : Data) (indices : List (Fin width)) :
    sign word state indices * sign word state indices = 1 := by
  induction indices with
  | nil => simp only [sign, mul_one]
  | cons index rest induction =>
      cases value : (word.bit index).get state <;> simp [sign, value, induction]

/-- The actual selected Z sequence cancels the same phase on a recomputed word. -/
theorem phaseCorrection_cancel_ket (word : EncodedBit.Word encoding width)
    (indices : List (Fin width)) (state : Data) :
    (sequence word indices).applyVec
        (sign word state indices •
          (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec) =
      (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  rw [UnitaryCircuit.applyVec_smul, phaseCorrection_sequence_ket, smul_smul,
    phaseCorrection_sign_square, one_smul]

/-- Every selected gate is charged at its original native Pauli-Z coordinate. -/
theorem phaseCorrection_sequence_trace (word : EncodedBit.Word encoding width)
    (indices : List (Fin width)) :
    (sequence word indices).eventTrace = List.replicate indices.length
      (Gate.atomicEvent (.declared "QuantumAlg.Components.Gate" "pauli-z")) := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      rw [sequence, UnitaryCircuit.seq_eventTrace, pauliZ_eventTrace, induction]
      rfl

/-- The same literal sequential program has one unit of depth per selected Z gate. -/
theorem phaseCorrection_sequence_depth (word : EncodedBit.Word encoding width)
    (indices : List (Fin width)) :
    (sequence word indices).evaluatedEventDepth (fun _ => 1) = indices.length := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      rw [sequence, UnitaryCircuit.evaluatedEventDepth_seq, induction]
      change 1 + rest.length = rest.length + 1
      omega

/-- The complete original register remains live, including every unselected position. -/
theorem phaseCorrection_sequence_physical (word : EncodedBit.Word encoding width)
    (indices : List (Fin width)) :
    (sequence word indices).physical_idx = List.range encoding.width := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      change UnitaryCircuit.unionPhysicalIdx [(word.bit index).wire.val]
        (sequence word rest).physical_idx = _
      rw [induction]
      apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
      intro wire member
      have same : wire = (word.bit index).wire.val := List.mem_singleton.mp member
      rw [same, List.mem_range]
      exact (word.bit index).wire.isLt

/-- An individual classical result selects precisely its one-bit positions. -/
def selected (outcome : Fin width → Bool) : List (Fin width) :=
  (List.finRange width).filter outcome

/-- Actual unitary branch for a previously read classical result. -/
def program (word : EncodedBit.Word encoding width) (outcome : Fin width → Bool) :
    UnitaryCircuit (Qubits encoding.width) := sequence word (selected outcome)

/-- The selected correction cannot execute more than one Z gate per word position. -/
theorem phaseCorrection_selected_count_le (outcome : Fin width → Bool) :
    (selected outcome).length ≤ width := by
  simpa only [selected, List.length_finRange] using
    List.length_filter_le outcome (List.finRange width)

end

end QuantumAlg.EncodedBit.Word.PhaseCorrection
