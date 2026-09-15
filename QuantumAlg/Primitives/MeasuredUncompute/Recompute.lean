/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Character
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual recomputation, selected Z correction, and inverse recomputation

The same native unitary computes a word and later uncomputes it. Between
these operations, the literal Z gates selected by a previously stored
measurement outcome supply the exact measured character. The resulting
full-state equation cancels that character without discarding a relative
phase or a live register [LYL+26, sec_point_add/sec_point_add.tex:85-105].

The realization premise is an internal composition interface for the
actual arithmetic program. Concrete arithmetic must establish it on the
original input domain; this lemma does not replace that program by an oracle.
-/

namespace QuantumAlg.MeasuredUncompute.Recompute

noncomputable section

open EncodedBit.Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Recompute, execute the literal selected phases, and run the same recomputation backwards. -/
def program (compute : UnitaryCircuit (Qubits encoding.width))
    (word : EncodedBit.Word encoding width) (mask : Fin width → Bool) :
    UnitaryCircuit (Qubits encoding.width) :=
  compute.seq ((PhaseCorrection.program word mask).seq compute.dagger)

/-- The actual inverse restores the complete original label after the selected phase. -/
theorem recompute_phase_ket (compute : UnitaryCircuit (Qubits encoding.width))
    {step : Data → Data} (realizes : UnitaryCircuit.Realizes encoding compute step)
    (word : EncodedBit.Word encoding width) (mask : Fin width → Bool) (state : Data) :
    (program compute word mask).applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      PhaseCorrection.sign word (step state) (PhaseCorrection.selected mask) •
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  have forward := realizes.apply_encoded_ket state
  have backward : compute.dagger.applyNormalized
      (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode (step state))) =
        NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state) :=
    (congrArg compute.dagger.applyNormalized forward).symm.trans
      (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized compute _)
  have forwardVec : compute.applyVec
      (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode (step state))).vec :=
    congrArg NormalizedVector.vec forward
  have backwardVec : compute.dagger.applyVec
      (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode (step state))).vec =
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec :=
    congrArg NormalizedVector.vec backward
  rw [program, UnitaryCircuit.applyVec_seq, forwardVec, UnitaryCircuit.applyVec_seq,
    PhaseCorrection.program, PhaseCorrection.phaseCorrection_sequence_ket,
    UnitaryCircuit.applyVec_smul, backwardVec]

/-- The recomputed word cancels exactly its earlier measurement character. -/
theorem recompute_cancels_measured_ket (compute : UnitaryCircuit (Qubits encoding.width))
    {step : Data → Data} (realizes : UnitaryCircuit.Realizes encoding compute step)
    (word : EncodedBit.Word encoding width) (state : Data) (value outcome : Fin (2 ^ width))
    (reads : ∀ index, (word.bit index).get (step state) = value.val.testBit index.val) :
    (program compute word (fun index => outcome.val.testBit index.val)).applyVec
        (WalshHadamard.walshSign outcome value •
          (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec) =
      (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  rw [UnitaryCircuit.applyVec_smul, recompute_phase_ket compute realizes,
    measuredCorrection_sign_walsh word (step state) value outcome reads, smul_smul,
    WalshHadamard.walshSign_mul_self, one_smul]

/-- Every external-reference column retains the same exact relative character. -/
theorem recompute_reference_entry (compute : UnitaryCircuit (Qubits encoding.width))
    {step : Data → Data} (realizes : UnitaryCircuit.Realizes encoding compute step)
    (word : EncodedBit.Word encoding width) (mask : Fin width → Bool) (state : Data)
    {Reference : Register} (row : Fin (2 ^ encoding.width)) (left right : Reference.Index) :
    UnitaryOperator.prodTensor (program compute word mask).matrix
        (1 : UnitaryOperator Reference) (row, left) (encoding.encode state, right) =
      if row = encoding.encode state ∧ left = right then
        PhaseCorrection.sign word (step state) (PhaseCorrection.selected mask) else 0 := by
  have column := congrArg (fun vector : HilbertVector (Qubits encoding.width) => vector row)
    (recompute_phase_ket compute realizes word mask state)
  have matrixColumn :=
    (HilbertOperator.applyVec_ket ((program compute word mask).matrix :
      HilbertOperator (Qubits encoding.width)) (encoding.encode state) row).symm.trans column
  rw [UnitaryOperator.prodTensor_apply, matrixColumn]
  simp only [PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply]
  change (PhaseCorrection.sign word (step state) (PhaseCorrection.selected mask) *
      (if row = encoding.encode state then 1 else 0)) *
      (if left = right then 1 else 0) = _
  by_cases selected : row = encoding.encode state <;> by_cases reference : left = right <;>
    simp [selected, reference]

end

end QuantumAlg.MeasuredUncompute.Recompute
