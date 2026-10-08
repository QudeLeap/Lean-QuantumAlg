/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage
import all QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Suffix.Matrix
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact native inverse-Fourier readout

The two native inverse QFTs act in parallel on the original disjoint exponent
registers. The group-value workspace remains an identity factor.
-/

namespace QuantumAlg.ShortDLP.DeclaredStage

noncomputable section

/-- The parallel inverse-QFT word has the tensor of the two actual inverse
circuits in the original exponent-register binary labels. -/
theorem readoutPair_binaryMatrix (oracles : OracleModel)
    (params : RegisterParameters) :
    (readoutPair oracles params).binaryMatrix =
      ((QuantumFourierTransform.Native.inverseCircuit oracles
        (firstBits params)).binaryMatrix).tensor
      ((QuantumFourierTransform.Native.inverseCircuit oracles
        params.ell).binaryMatrix) := by
  unfold readoutPair UnitaryCircuit.binaryMatrix
  rw [UnitaryCircuit.parallel_matrix_raw,
    UnitaryOperator.unitaryOperator_reindex_mul]
  change (UnitaryCircuit.onBinarySuffix (firstBits params)
      (QuantumFourierTransform.Native.inverseCircuit oracles params.ell)).binaryMatrix *
    (UnitaryCircuit.onBinaryPrefix params.ell
      (QuantumFourierTransform.Native.inverseCircuit oracles
        (firstBits params))).binaryMatrix = _
  rw [UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  apply Subtype.ext
  change HilbertOperator.tensor
      (1 : HilbertOperator (Qubits (firstBits params)))
      (QuantumFourierTransform.Native.inverseCircuit oracles params.ell).binaryMatrix *
    HilbertOperator.tensor
      (QuantumFourierTransform.Native.inverseCircuit oracles
        (firstBits params)).binaryMatrix
      (1 : HilbertOperator (Qubits params.ell)) =
    HilbertOperator.tensor
      (QuantumFourierTransform.Native.inverseCircuit oracles
        (firstBits params)).binaryMatrix
      (QuantumFourierTransform.Native.inverseCircuit oracles params.ell).binaryMatrix
  rw [HilbertOperator.tensor_mul_tensor]
  simp

/-- Both actual inverse words realize the source inverse-Fourier matrices. -/
theorem readoutPair_sourceMatrix (oracles : OracleModel)
    (params : RegisterParameters) :
    (readoutPair oracles params).binaryMatrix =
      (star (QFTOperator (firstBits params))).tensor
        (star (QFTOperator params.ell)) := by
  rw [readoutPair_binaryMatrix]
  rw [← QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
      oracles (firstBits params),
    ← QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
      oracles params.ell]
  rfl

/-- The declared stage's complete readout preserves the original group
workspace while both inverse Fourier words act on their own exponent registers. -/
theorem readout_binaryMatrix {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits) :
    (readout encoding).binaryMatrix =
      ((star (QFTOperator (firstBits params))).tensor
        (star (QFTOperator params.ell))).tensor
          (1 : UnitaryOperator (Qubits params.workspaceBits)) := by
  rw [readout, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    readoutPair_sourceMatrix]

end

end QuantumAlg.ShortDLP.DeclaredStage
