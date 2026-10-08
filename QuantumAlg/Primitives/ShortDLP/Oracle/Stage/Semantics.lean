/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Primitives.WalshHadamard.Pipeline
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact native preparation of the short-DLP registers

The declared stage uses the native parallel Hadamard word. Its binary operator
has the original Walsh matrix on both exponent registers and the identity on
the untouched group-value workspace.
-/

namespace QuantumAlg.ShortDLP.DeclaredStage

noncomputable section

/-- The actual native preparation is the source Hadamard operator on the
combined exponent registers, with the original workspace left untouched. -/
theorem prepare_binaryMatrix {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits) :
    (prepare encoding).binaryMatrix =
      (WalshHadamard.hadamardLayerOperator
        (firstBits params + params.ell)).tensor
          (1 : UnitaryOperator (Qubits params.workspaceBits)) := by
  rw [prepare, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  exact congrArg
    (fun operator : UnitaryOperator (Qubits (firstBits params + params.ell)) =>
      operator.tensor (1 : UnitaryOperator (Qubits params.workspaceBits)))
    (WalshHadamard.Native.native_binary_matrix
      (declaredModel encoding) (firstBits params + params.ell))

/-- The actual preparation takes the zero exponent word and zero group
workspace to a uniform exponent word with that workspace still zero. -/
theorem prepare_binaryMatrix_apply_zero {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits) :
    (prepare encoding).binaryMatrix.apply
        (NormalizedVector.ket
          (prodEquiv
            ((0 : Fin (2 ^ (firstBits params + params.ell))),
              (0 : Fin (2 ^ params.workspaceBits))))) =
      (WalshHadamard.uniformState (firstBits params + params.ell)).tensor
        (NormalizedVector.ket (0 : Fin (2 ^ params.workspaceBits))) := by
  rw [← NormalizedVector.tensor_ket, prepare_binaryMatrix,
    UnitaryOperator.tensor_apply_tensor,
    WalshHadamard.hadamardLayerOperator_apply_zero,
    UnitaryOperator.one_apply]

end

end QuantumAlg.ShortDLP.DeclaredStage
