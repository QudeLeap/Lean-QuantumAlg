/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source.NoSwapMatrix
public import QuantumAlg.Primitives.QFT.Source.Reverse.Matrix
import all QuantumAlg.Primitives.QFT.Source.NoSwapMatrix
import all QuantumAlg.Primitives.QFT.Source.Reverse.Matrix
import all QuantumAlg.Primitives.QFT.Source.Matrix
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Exact Fourier matrix of the complete native construction

The recursive native source circuit followed by its final SWAP instructions
realizes the normalized positive-phase Fourier operator at every width.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

public lemma qftSource_circuit_binaryMatrix (oracles : OracleModel) (n : Nat)
    (environment : oracles.Interpretation) :
    onBinaryLabels (circuit oracles n) environment = QFTOperator n := by
  apply Subtype.ext
  ext output input
  rw [circuit, qftSource_binaryMatrix_seq (environment := environment),
    qftSource_reverse_binaryMatrix (environment := environment)]
  change Matrix.mulVec ((qftReverseBitsPerm n).permMatrix Complex)
    (fun row => onBinaryLabels (noSwap oracles n) environment row input) output = _
  rw [Matrix.permMatrix_mulVec]
  change onBinaryLabels (noSwap oracles n) environment (qftReverseBits n output) input =
    (QFTOperator n : HilbertOperator (Qubits n)) output input
  rw [qftSource_noSwap_binaryMatrix_entry (environment := environment),
    qftReverseBits_involutive, QFTOperator_entry]

public lemma qftSource_circuit_physicalMatrix (oracles : OracleModel) (n : Nat)
    (environment : oracles.Interpretation) :
    ((circuit oracles n).matrix environment) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm (QFTOperator n) := by
  have original := qftSource_circuit_binaryMatrix (environment := environment) oracles n
  have transported := congrArg
    (UnitaryOperator.reindex (R := Qubits n) (S := (QFTPrimitive.layout n).register)
      (QuantumSignature.qubitsIndexEquiv n).symm) original
  exact (UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n) ((circuit oracles n).matrix environment)).symm.trans
      transported

end

end QuantumAlg.QuantumFourierTransform.Source
