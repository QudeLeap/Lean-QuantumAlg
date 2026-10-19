/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Native
public import QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
public import QuantumAlg.Primitives.WalshHadamard.Mathematics
import all QuantumAlg.Algorithms.OrderFinding.Native
import all QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Exact binary matrix of the source order-finding word

The phase Hadamards and inverse Fourier transform act on the original prefix.
The middle operator is precisely the declared modular-exponentiation XOR query,
with the target register preserved in both surrounding stages
[dW19, qcnotes.tex:2203-2225].
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

/-- The parallel native Hadamards have the original full-register action. -/
public lemma initialLayer_binaryMatrix (t width : Nat)
    (environment : (sourceModel t width).Interpretation) :
    (initialLayer t width).binaryMatrix environment =
      (WalshHadamard.hadamardLayerOperator t).tensor
        (1 : UnitaryOperator (Qubits width)) := by
  rw [initialLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  exact congrArg (fun operator : UnitaryOperator (Qubits t) =>
    operator.tensor (1 : UnitaryOperator (Qubits width)))
      (WalshHadamard.Native.native_binary_matrix (sourceModel t width) t environment)

/-- The granted source call denotes the original XOR permutation exactly. -/
public lemma oracleLayer_binaryMatrix {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (oracleLayer t width).binaryMatrix (interpretation access) = modExpOracle access := by
  unfold UnitaryCircuit.binaryMatrix
  rw [oracleLayer, UnitarySource.Circuit.program_matrix]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (t + width))
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (t + width)).symm
      (modExpOracle access)) = modExpOracle access
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (t + width)).symm (modExpOracle access)

/-- The generated adjoint has the exact inverse Fourier action on the prefix. -/
public lemma readoutLayer_binaryMatrix (t width : Nat)
    (environment : (sourceModel t width).Interpretation) :
    (readoutLayer t width).binaryMatrix environment =
      (star (QFTOperator t)).tensor (1 : UnitaryOperator (Qubits width)) := by
  rw [readoutLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  apply congrArg (fun operator : UnitaryOperator (Qubits t) =>
    operator.tensor (1 : UnitaryOperator (Qubits width)))
  change QuantumFourierTransform.Native.onBinaryLabels
    (QuantumFourierTransform.Native.inverseCircuit (sourceModel t width) t) environment =
      star (QFTOperator t)
  exact QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix
    (sourceModel t width) t environment

/-- One actual source word has the exact three-stage order-finding operator. -/
public lemma circuit_binaryMatrix {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (circuit t width).binaryMatrix (interpretation access) =
      (star (QFTOperator t)).tensor (1 : UnitaryOperator (Qubits width)) *
        (modExpOracle access *
          (WalshHadamard.hadamardLayerOperator t).tensor
            (1 : UnitaryOperator (Qubits width))) := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    initialLayer_binaryMatrix, oracleLayer_binaryMatrix, readoutLayer_binaryMatrix]

end

end QuantumAlg.OrderFinding.Native
