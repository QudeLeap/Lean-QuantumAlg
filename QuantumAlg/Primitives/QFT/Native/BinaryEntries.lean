/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native.Matrix
import all QuantumAlg.Primitives.QFT.Native.Matrix
import all QuantumAlg.Primitives.QFT.Native.LeadingEntries
import all QuantumAlg.Primitives.QFT.Native.TailEntries
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis.Pair
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow.BitReverse

/-!
# Recursive native entries in the original paired binary labels

The first bit and the lower integer label encode precisely the native
coordinate split. This connects the actual leading and tail operations to
the matrix recurrence used for the Fourier transform.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

private theorem binary_pair_decode (n : Nat) (head : Fin 2) (tail : Fin (2 ^ n)) :
    (QuantumSignature.qubitsIndexEquiv (n + 1)).symm (qftPairEquiv n (head, tail)) =
      Fin.cons head ((QuantumSignature.qubitsIndexEquiv n).symm tail) := by
  have encoded := BinaryBasis.bigEndianEquiv_cons_pair n head
    ((QuantumSignature.qubitsIndexEquiv n).symm tail)
  change QuantumSignature.qubitsIndexEquiv (n + 1)
      (Fin.cons head ((QuantumSignature.qubitsIndexEquiv n).symm tail)) =
    qftPairEquiv n (head, QuantumSignature.qubitsIndexEquiv n
      ((QuantumSignature.qubitsIndexEquiv n).symm tail)) at encoded
  rw [Equiv.apply_symm_apply] at encoded
  exact (congrArg (QuantumSignature.qubitsIndexEquiv (n + 1)).symm encoded.symm).trans
    ((QuantumSignature.qubitsIndexEquiv (n + 1)).symm_apply_apply _)

theorem qftNative_binaryMatrix_pair {oracles : OracleModel} {n : Nat}
    (body : UnitaryCircuit AlgorithmGate.model oracles (QFTPrimitive.layout (n + 1)))
    (rowHead columnHead : Fin 2) (rowTail columnTail : Fin (2 ^ n)) :
    onBinaryLabels body (qftPairEquiv n (rowHead, rowTail))
        (qftPairEquiv n (columnHead, columnTail)) =
      body.matrix (Fin.cons rowHead ((QuantumSignature.qubitsIndexEquiv n).symm rowTail))
        (Fin.cons columnHead ((QuantumSignature.qubitsIndexEquiv n).symm columnTail)) := by
  change body.matrix
    ((QuantumSignature.qubitsIndexEquiv (n + 1)).symm (qftPairEquiv n (rowHead, rowTail)))
    ((QuantumSignature.qubitsIndexEquiv (n + 1)).symm
      (qftPairEquiv n (columnHead, columnTail))) = _
  rw [binary_pair_decode, binary_pair_decode]

theorem qftNative_leading_binaryMatrix_pair (oracles : OracleModel) (n : Nat)
    (rowHead columnHead : Fin 2) (rowTail columnTail : Fin (2 ^ n)) :
    onBinaryLabels (leadingHadamard oracles n) (qftPairEquiv n (rowHead, rowTail))
        (qftPairEquiv n (columnHead, columnTail)) =
      if rowTail = columnTail then Gate.HOp rowHead columnHead else 0 := by
  classical
  refine (qftNative_binaryMatrix_pair (leadingHadamard oracles n)
    rowHead columnHead rowTail columnTail).trans ?_
  refine (qftNative_leading_matrix_cons oracles n rowHead columnHead
    ((QuantumSignature.qubitsIndexEquiv n).symm rowTail)
    ((QuantumSignature.qubitsIndexEquiv n).symm columnTail)).trans ?_
  let value : Complex := Gate.HOp rowHead columnHead
  change value *
    (if ((QuantumSignature.qubitsIndexEquiv n).symm rowTail : Fin n → Fin 2) =
      ((QuantumSignature.qubitsIndexEquiv n).symm columnTail : Fin n → Fin 2) then 1 else 0) =
    if rowTail = columnTail then value else 0
  by_cases same : rowTail = columnTail
  · rw [if_pos (congrArg (QuantumSignature.qubitsIndexEquiv n).symm same), if_pos same,
      mul_one]
  · have different : (QuantumSignature.qubitsIndexEquiv n).symm rowTail ≠
        (QuantumSignature.qubitsIndexEquiv n).symm columnTail :=
      fun equal => same ((QuantumSignature.qubitsIndexEquiv n).symm.injective equal)
    rw [if_neg different, if_neg same, mul_zero]

theorem qftNative_tail_binaryMatrix_pair (oracles : OracleModel) (n : Nat)
    (body : UnitaryCircuit AlgorithmGate.model oracles (QFTPrimitive.layout n))
    (rowHead columnHead : Fin 2) (rowTail columnTail : Fin (2 ^ n)) :
    onBinaryLabels (tailLayer oracles n body) (qftPairEquiv n (rowHead, rowTail))
        (qftPairEquiv n (columnHead, columnTail)) =
      if rowHead = columnHead then onBinaryLabels body rowTail columnTail else 0 := by
  refine (qftNative_binaryMatrix_pair (tailLayer oracles n body)
    rowHead columnHead rowTail columnTail).trans ?_
  refine (qftNative_tail_matrix_cons oracles n body rowHead columnHead
    ((QuantumSignature.qubitsIndexEquiv n).symm rowTail)
    ((QuantumSignature.qubitsIndexEquiv n).symm columnTail)).trans ?_
  change onBinaryLabels body rowTail columnTail * (if rowHead = columnHead then 1 else 0) = _
  split <;> simp_all

end

end QuantumAlg.QuantumFourierTransform.Native
