/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native.NoSwapMatrix
public import QuantumAlg.Primitives.QFT.Native.ReverseMatrix
import all QuantumAlg.Primitives.QFT.Native.NoSwapMatrix
import all QuantumAlg.Primitives.QFT.Native.ReverseMatrix
import all QuantumAlg.Primitives.QFT.Native.Matrix
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Exact Fourier matrix of the complete native construction

The recursively expanded word followed by its three-CNOT swaps realizes
the original normalized positive-phase Fourier operator at every width.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

public theorem qftNative_circuit_binaryMatrix (oracles : OracleModel) (n : Nat) :
    onBinaryLabels (circuit oracles n) = QFTOperator n := by
  apply Subtype.ext
  ext output input
  rw [circuit, qftNative_binaryMatrix_seq, qftNative_reverse_binaryMatrix]
  change Matrix.mulVec ((qftReverseBitsPerm n).permMatrix Complex)
    (fun row => onBinaryLabels (noSwap oracles n) row input) output = _
  rw [Matrix.permMatrix_mulVec]
  change onBinaryLabels (noSwap oracles n) (qftReverseBits n output) input =
    (QFTOperator n : HilbertOperator (Qubits n)) output input
  rw [qftNative_noSwap_binaryMatrix_entry, qftReverseBits_involutive, QFTOperator_entry]

public theorem qftNative_circuit_physicalMatrix (oracles : OracleModel) (n : Nat) :
    (circuit oracles n).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm (QFTOperator n) := by
  have original := qftNative_circuit_binaryMatrix oracles n
  have transported := congrArg
    (UnitaryOperator.reindex (R := Qubits n) (S := (QFTPrimitive.layout n).register)
      (QuantumSignature.qubitsIndexEquiv n).symm) original
  exact (UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n) (circuit oracles n).matrix).symm.trans transported

end

end QuantumAlg.QuantumFourierTransform.Native
