/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source.FourierMatrix
public import QuantumAlg.Primitives.QFT.Native.Matrix
import all QuantumAlg.Primitives.QFT.Source.FourierMatrix
import all QuantumAlg.Primitives.QFT.Native.Matrix
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Lowering
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Exact Fourier matrix of the complete native construction

The recursively expanded word followed by its three-CNOT swaps realizes
the original normalized positive-phase Fourier operator at every width.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

public lemma qftNative_circuit_binaryMatrix (oracles : OracleModel) (n : Nat)
    (environment : oracles.Interpretation) :
    onBinaryLabels (circuit oracles n) environment = QFTOperator n := by
  unfold onBinaryLabels circuit
  rw [Lowering.lower_matrix]
  exact Source.qftSource_circuit_binaryMatrix .empty n OracleModel.emptyInterpretation

public lemma qftNative_circuit_physicalMatrix (oracles : OracleModel) (n : Nat)
    (environment : oracles.Interpretation) :
    ((circuit oracles n).matrix environment) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm (QFTOperator n) := by
  have original := qftNative_circuit_binaryMatrix (environment := environment) oracles n
  have transported := congrArg
    (UnitaryOperator.reindex (R := Qubits n) (S := (QFTPrimitive.layout n).register)
      (QuantumSignature.qubitsIndexEquiv n).symm) original
  exact (UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n) ((circuit oracles n).matrix environment)).symm.trans
      transported

end

end QuantumAlg.QuantumFourierTransform.Native
