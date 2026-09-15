/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.CoherentMeasurement
import all QuantumAlg.Primitives.MeasuredUncompute.StoredWordReset

/-!
# The measured character survives the actual selected word reset

The literal X sequence selected by the stored Z outcome maps the measured
word to zero. Composing it with the actual Hadamard and Z matrices leaves
the exact character on every remaining-system amplitude, including all
external-reference correlations [LYL+26, sec_point_add/sec_point_add.tex:67-81].

These equations supply the branch calculation for the existing circuit
interpreter's measurement-write-read-selection composition. They neither
provide a measurement result independently of that execution nor release
the reset word.
-/

namespace QuantumAlg.MeasuredUncompute

noncomputable section

/-- The selected literal reset maps the measured ket to zero and preserves its reference label. -/
theorem storedWordReset_reference_ket {width : Nat} (outcome : Fin (2 ^ width))
    {Reference : Register} (reference : Reference.Index) :
    (UnitaryOperator.prodTensor (StoredWordReset.program outcome).matrix
      (1 : UnitaryOperator Reference)).applyVec
        (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
          (outcome, reference)).vec =
      (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
        (0, reference)).vec := by
  ext index
  rcases index with ⟨row, other⟩
  change HilbertOperator.applyVec
    (UnitaryOperator.prodTensor (StoredWordReset.program outcome).matrix
      (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod (Qubits width) Reference))
    (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
      (outcome, reference)).vec (row, other) = _
  rw [HilbertOperator.applyVec_ket, StoredWordReset.storedWordReset_reference_entry]
  by_cases selected : row = 0 ∧ other = reference
  · obtain ⟨rfl, rfl⟩ := selected
    simp [NormalizedVector.ket_apply]
  · have different : ((row, other) : (Register.prod (Qubits width) Reference).Index) ≠
        (0, reference) := by
      intro same
      exact selected ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
    simp [NormalizedVector.ket_apply, selected, different]

/-- Actual Hadamard, Z projection and selected X reset retain the exact input-dependent phase. -/
theorem measuredReset_reference_ket (width : Nat) {Reference : Register}
    (outcome value : Fin (2 ^ width)) (reference : Reference.Index) :
    (UnitaryOperator.prodTensor (StoredWordReset.program outcome).matrix
      (1 : UnitaryOperator Reference)).applyVec
        ((measuredOperator width Reference outcome).applyVec
          (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
            (value, reference)).vec) =
      (WalshHadamard.invSqrtCard width * WalshHadamard.walshSign outcome value) •
        (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
          (0, reference)).vec := by
  rw [measuredHadamard_reference_ket, UnitaryOperator.applyVec_smul,
    storedWordReset_reference_ket]

/-- Arbitrary coherent correlations survive reset with precisely the character later corrected. -/
theorem measuredReset_coherent_reference (width : Nat) {Reference : Register}
    (outcome : Fin (2 ^ width)) (value : Reference.Index → Fin (2 ^ width))
    (amplitude : Reference.Index → ℂ) :
    (UnitaryOperator.prodTensor (StoredWordReset.program outcome).matrix
      (1 : UnitaryOperator Reference)).applyVec
        ((measuredOperator width Reference outcome).applyVec
          (∑ reference : Reference.Index, amplitude reference •
            (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
              (value reference, reference)).vec)) =
      ∑ reference : Reference.Index,
        (amplitude reference *
          (WalshHadamard.invSqrtCard width * WalshHadamard.walshSign outcome (value reference))) •
            (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
              (0, reference)).vec := by
  rw [measuredHadamard_coherent_reference]
  change HilbertOperator.applyVec
    (UnitaryOperator.prodTensor (StoredWordReset.program outcome).matrix
      (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod (Qubits width) Reference))
      _ = _
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro reference _
  rw [HilbertOperator.applyVec_smul]
  exact congrArg (fun vector =>
    (amplitude reference *
      (WalshHadamard.invSqrtCard width * WalshHadamard.walshSign outcome (value reference))) •
        vector) (storedWordReset_reference_ket outcome reference)

end

end QuantumAlg.MeasuredUncompute
