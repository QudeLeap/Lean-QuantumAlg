/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native.Inverse.Matrix
public import QuantumAlg.Primitives.QFT.Native.FourierMatrix
public import QuantumAlg.Primitives.QFT.Native.Matrix
public import QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Primitives.QFT.Native.Inverse.Matrix
import all QuantumAlg.Core.Base.Gate.Unitary.Adjoint

/-!
# Original inverse Fourier target of the explicit native word

The normalized negative-phase Fourier transform is the adjoint of the original
positive-phase matrix [dW19, qcnotes.tex:1705]. Both equalities concern the
actual inverse circuit, including the reversal of the final wire swaps.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

public theorem qftNative_inverseCircuit_binaryMatrix (oracles : OracleModel) (n : Nat) :
    onBinaryLabels (inverseCircuit oracles n) = star (QFTOperator n) := by
  unfold onBinaryLabels
  rw [qftNative_inverseCircuit_matrix, UnitaryOperator.unitaryOperator_reindex_star]
  exact congrArg star (qftNative_circuit_binaryMatrix .empty n)

public theorem qftNative_inverseCircuit_physicalMatrix (oracles : OracleModel) (n : Nat) :
    (inverseCircuit oracles n).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm
        (star (QFTOperator n)) := by
  rw [qftNative_inverseCircuit_matrix, qftNative_circuit_physicalMatrix,
    UnitaryOperator.unitaryOperator_reindex_star]

end

end QuantumAlg.QuantumFourierTransform.Native
