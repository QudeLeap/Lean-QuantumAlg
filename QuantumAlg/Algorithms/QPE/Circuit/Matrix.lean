/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Circuit
import all QuantumAlg.Algorithms.QPE.Circuit
import all QuantumAlg.Algorithms.QPE.Query.Ladder.Matrix
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Readout
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Primitives.WalshHadamard.Mathematics
import all QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Primitives.QFT.Native.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Exact full matrix of the native phase-estimation word

The actual stages retain the original Hadamard, source-power and inverse
Fourier operators on the entire phase/source register, including global phase
[Lin22, phaseestimation.tex:514-523,647-670].
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

/-- The real phase Hadamards tensor the identity on the whole source register. -/
theorem qpeNative_initialLayer_binaryMatrix (phaseWidth : Nat) {systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) :
    (initialLayer phaseWidth unitary).binaryMatrix =
      (WalshHadamard.hadamardLayerOperator phaseWidth).tensor
        (1 : UnitaryOperator (Qubits systemWidth)) := by
  rw [initialLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  exact congrArg (fun operator : UnitaryOperator (Qubits phaseWidth) =>
    operator.tensor (1 : UnitaryOperator (Qubits systemWidth)))
    (WalshHadamard.Native.native_binary_matrix (UnitarySource.model unitary true) phaseWidth)

/-- The real inverse Fourier word tensors the identity on the same source systems. -/
theorem qpeNative_readoutLayer_binaryMatrix (phaseWidth : Nat) {systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) :
    (readoutLayer phaseWidth unitary).binaryMatrix =
      (invQFT phaseWidth).tensor (1 : UnitaryOperator (Qubits systemWidth)) := by
  rw [readoutLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  apply congrArg (fun operator : UnitaryOperator (Qubits phaseWidth) =>
    operator.tensor (1 : UnitaryOperator (Qubits systemWidth)))
  change QuantumFourierTransform.Native.onBinaryLabels
    (qpeReadoutCircuit (UnitarySource.model unitary true) phaseWidth) = invQFT phaseWidth
  rw [qpeReadoutCircuit, QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix,
    qpeReadout_binary_matrix]

/-- The full actual native word has exactly the original three-stage QPE matrix. -/
theorem qpeNative_circuit_binaryMatrix (phaseWidth : Nat) {systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) :
    (circuit phaseWidth unitary).binaryMatrix =
      (invQFT phaseWidth).tensor (1 : UnitaryOperator (Qubits systemWidth)) *
        (qpeControlledPowerOp phaseWidth unitary *
          (WalshHadamard.hadamardLayerOperator phaseWidth).tensor
            (1 : UnitaryOperator (Qubits systemWidth))) := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, qpeNative_initialLayer_binaryMatrix,
    qpeNative_queryLadder_binaryMatrix, qpeNative_readoutLayer_binaryMatrix]

end

end QuantumAlg.QuantumPhaseEstimation.Native
