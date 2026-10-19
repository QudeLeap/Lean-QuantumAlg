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
lemma readoutPair_binaryMatrix (oracles : OracleModel)
    (params : RegisterParameters) (interpretation : oracles.Interpretation) :
    ((readoutPair oracles params).binaryMatrix interpretation) =
      ((QuantumFourierTransform.Native.inverseCircuit oracles
        (firstBits params)).binaryMatrix interpretation).tensor
      ((QuantumFourierTransform.Native.inverseCircuit oracles
        params.ell).binaryMatrix interpretation) := by
  unfold readoutPair UnitaryCircuit.binaryMatrix
  rw [UnitaryCircuit.parallel_matrix_raw,
    UnitaryOperator.unitaryOperator_reindex_mul]
  change (UnitaryCircuit.onBinarySuffix (firstBits params)
      (QuantumFourierTransform.Native.inverseCircuit oracles params.ell)).binaryMatrix
        interpretation *
    (UnitaryCircuit.onBinaryPrefix params.ell
      (QuantumFourierTransform.Native.inverseCircuit oracles
        (firstBits params))).binaryMatrix interpretation = _
  rw [UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  apply Subtype.ext
  change HilbertOperator.tensor
      (1 : HilbertOperator (Qubits (firstBits params)))
      ((QuantumFourierTransform.Native.inverseCircuit oracles params.ell).binaryMatrix
        interpretation) *
    HilbertOperator.tensor
      ((QuantumFourierTransform.Native.inverseCircuit oracles
        (firstBits params)).binaryMatrix interpretation)
      (1 : HilbertOperator (Qubits params.ell)) =
    HilbertOperator.tensor
      ((QuantumFourierTransform.Native.inverseCircuit oracles
        (firstBits params)).binaryMatrix interpretation)
      ((QuantumFourierTransform.Native.inverseCircuit oracles params.ell).binaryMatrix
        interpretation)
  rw [HilbertOperator.tensor_mul_tensor]
  simp

/-- Both actual inverse words realize the source inverse-Fourier matrices. -/
lemma readoutPair_sourceMatrix (oracles : OracleModel)
    (params : RegisterParameters) (interpretation : oracles.Interpretation) :
    ((readoutPair oracles params).binaryMatrix interpretation) =
      (star (QFTOperator (firstBits params))).tensor
        (star (QFTOperator params.ell)) := by
  rw [readoutPair_binaryMatrix]
  rw [← QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
      oracles (firstBits params) interpretation,
    ← QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
      oracles params.ell interpretation]
  rfl

/-- The declared stage's complete readout preserves the original group
workspace while both inverse Fourier words act on their own exponent registers. -/
lemma readout_binaryMatrix (N : Nat) (params : RegisterParameters)
    (interpretation : (declaredModel N params).Interpretation) :
    ((readout N params).binaryMatrix interpretation) =
      ((star (QFTOperator (firstBits params))).tensor
        (star (QFTOperator params.ell))).tensor
          (1 : UnitaryOperator (Qubits params.workspaceBits)) := by
  rw [readout, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    readoutPair_sourceMatrix]

end

end QuantumAlg.ShortDLP.DeclaredStage
