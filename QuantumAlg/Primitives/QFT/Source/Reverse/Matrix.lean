/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source.Matrix
import all QuantumAlg.Primitives.QFT.Source.Matrix
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Primitives.QFT.Mathematics.BitReverse
import all QuantumAlg.Components.Gates.Swap.Label
import all QuantumAlg.Components.Gates.Swap.Operator
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Components.Kets

/-!
# The complete native bit-reversal operator

Each symmetric swap is one native source instruction in the actual disjoint
parallel word. Its complete operator agrees with the bit-reversal permutation
on every computational label.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

private lemma swapStep_binaryMatrix (oracles : OracleModel) (n : Nat)
    (index : Fin (n / 2))
    (environment : oracles.Interpretation) :
    onBinaryLabels (swapStep oracles n index) environment =
      qftSwapOperator (qftSwapLeft n index) (qftSwapRight n index)
        (qftSwapLeft_ne_right n index) :=
  qftSource_primitive_binaryMatrix (environment := environment) oracles _

private lemma reversePrefix_binary_apply_ket (oracles : OracleModel) (n count : Nat)
    (bounded : count ≤ n / 2) (label : Fin (2 ^ n))
    (environment : oracles.Interpretation) :
    (onBinaryLabels (reversePrefix oracles n count bounded) environment).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n)
        (qftBitReverseLabelPrefix n count bounded label) : HilbertVector (Qubits n)) := by
  induction count with
  | zero =>
      have empty : onBinaryLabels (reversePrefix oracles n 0 bounded) environment = 1 := by
        rw [onBinaryLabels, reversePrefix_zero_matrix (environment := environment),
          UnitaryOperator.unitaryOperator_reindex_one]
      rw [empty, UnitaryOperator.one_applyVec]
      rfl
  | succ count ih =>
      have next : onBinaryLabels (reversePrefix oracles n (count + 1) bounded) environment =
          onBinaryLabels (swapStep oracles n ⟨count, Nat.lt_of_succ_le bounded⟩) environment *
            onBinaryLabels
              (reversePrefix oracles n count (Nat.le_of_succ_le bounded)) environment := by
        unfold onBinaryLabels
        rw [reversePrefix_succ_matrix (environment := environment),
          UnitaryOperator.unitaryOperator_reindex_mul]
      rw [next, UnitaryOperator.mul_applyVec, ih, swapStep_binaryMatrix (environment :=
        environment),
        qftSwapOperator_applyVec_ket]
      rfl

lemma qftSource_reverse_binary_apply_ket (oracles : OracleModel) (n : Nat)
    (label : Fin (2 ^ n))
    (environment : oracles.Interpretation) :
    (onBinaryLabels (bitReverse oracles n) environment).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n) (qftReverseBits n label) :
        HilbertVector (Qubits n)) := by
  rw [bitReverse, reversePrefix_binary_apply_ket (environment := environment),
    qftBitReverseLabel_eq]

lemma qftSource_reverse_binaryMatrix (oracles : OracleModel) (n : Nat)
    (environment : oracles.Interpretation) :
    onBinaryLabels (bitReverse oracles n) environment =
      UnitaryOperator.ofPerm (qftReverseBitsPerm n) := by
  apply Subtype.ext
  ext output input
  have actual := congrArg (fun state : HilbertVector (Qubits n) => state output)
    (qftSource_reverse_binary_apply_ket (environment := environment) oracles n input)
  have target := congrArg (fun state : HilbertVector (Qubits n) => state output)
    (UnitaryOperator.ofPerm_applyVec_ket (qftReverseBitsPerm n) input)
  have inverse : (qftReverseBitsPerm n)⁻¹ input = qftReverseBits n input := rfl
  rw [inverse] at target
  simpa [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using actual.trans target.symm

end

end QuantumAlg.QuantumFourierTransform.Source
