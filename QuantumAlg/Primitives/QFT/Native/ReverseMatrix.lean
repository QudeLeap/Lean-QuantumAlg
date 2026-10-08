/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native.Matrix
import all QuantumAlg.Primitives.QFT.Native.Matrix
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Primitives.QFT.Mathematics.BitReverse
import all QuantumAlg.Components.Gates.Swap.Label
import all QuantumAlg.Components.Gates.Swap.Operator
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Components.Kets

/-!
# The complete native bit-reversal operator

Each symmetric swap executes its three CNOTs. Their composed action agrees
with the original bit-reversal permutation on every computational label.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

private theorem swapStep_binaryMatrix (oracles : OracleModel) (n : Nat)
    (index : Fin (n / 2)) :
    onBinaryLabels (swapStep oracles n index) =
      qftSwapOperator (qftSwapLeft n index) (qftSwapRight n index)
        (qftSwapLeft_ne_right n index) :=
  qftNative_primitive_binaryMatrix oracles _

private theorem reversePrefix_binary_apply_ket (oracles : OracleModel) (n count : Nat)
    (bounded : count ≤ n / 2) (label : Fin (2 ^ n)) :
    (onBinaryLabels (reversePrefix oracles n count bounded)).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n)
        (qftBitReverseLabelPrefix n count bounded label) : HilbertVector (Qubits n)) := by
  induction count with
  | zero =>
      rw [reversePrefix, qftNative_binaryMatrix_identity, UnitaryOperator.one_applyVec]
      rfl
  | succ count ih =>
      rw [reversePrefix, qftNative_binaryMatrix_seq, UnitaryOperator.mul_applyVec,
        ih, swapStep_binaryMatrix, qftSwapOperator_applyVec_ket]
      rfl

theorem qftNative_reverse_binary_apply_ket (oracles : OracleModel) (n : Nat)
    (label : Fin (2 ^ n)) :
    (onBinaryLabels (bitReverse oracles n)).applyVec
        (NormalizedVector.ket (R := Qubits n) label : HilbertVector (Qubits n)) =
      (NormalizedVector.ket (R := Qubits n) (qftReverseBits n label) :
        HilbertVector (Qubits n)) := by
  rw [bitReverse, reversePrefix_binary_apply_ket, qftBitReverseLabel_eq]

theorem qftNative_reverse_binaryMatrix (oracles : OracleModel) (n : Nat) :
    onBinaryLabels (bitReverse oracles n) =
      UnitaryOperator.ofPerm (qftReverseBitsPerm n) := by
  apply Subtype.ext
  ext output input
  have actual := congrArg (fun state : HilbertVector (Qubits n) => state output)
    (qftNative_reverse_binary_apply_ket oracles n input)
  have target := congrArg (fun state : HilbertVector (Qubits n) => state output)
    (UnitaryOperator.ofPerm_applyVec_ket (qftReverseBitsPerm n) input)
  have inverse : (qftReverseBitsPerm n)⁻¹ input = qftReverseBits n input := rfl
  rw [inverse] at target
  simpa [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using actual.trans target.symm

end

end QuantumAlg.QuantumFourierTransform.Native
