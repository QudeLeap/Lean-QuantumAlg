/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
public import QuantumAlg.Primitives.QFT.Native.Inverse.Resources
public import QuantumAlg.Primitives.QFT.Native.Inverse.Depth
import all QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Primitives.QFT.Native.Inverse.Resources
import all QuantumAlg.Primitives.QFT.Native.Inverse.Depth
import all QuantumAlg.Primitives.QFT.Native.Matrix
import all QuantumAlg.Primitives.QFT.Mathematics

/-!
# Native inverse Fourier readout for phase estimation

The readout uses the actual generic adjoint of the expanded Fourier word.
Its original binary-label operator is the negative-phase Fourier transform
[Lin22, phaseestimation.tex:647-670]. No oracle query is needed by this stage.
-/

namespace QuantumAlg

noncomputable section

/-- The actual inverse Fourier word in the phase register's physical layout. -/
public def qpeReadoutCircuit (oracles : OracleModel) (t : Nat) :=
  QuantumFourierTransform.Native.inverseCircuit oracles t

/-- Express the executed readout in the original binary basis used by phase analysis. -/
public def invQFT (t : Nat) : UnitaryOperator (Qubits t) :=
  QuantumFourierTransform.Native.onBinaryLabels (qpeReadoutCircuit .empty t)

/-- The complete readout has exactly the original inverse Fourier matrix. -/
theorem qpeReadout_binary_matrix (t : Nat) : invQFT t = star (QFTOperator t) :=
  QuantumFourierTransform.Native.qftNative_inverseCircuit_binaryMatrix .empty t

/-- Native counts include every phase and swap expansion and no query. -/
public theorem qpeReadout_native_event_count (oracles : OracleModel)
    (event : Resource.Event (.quantum AlgorithmGate.model oracles)) (t : Nat) :
    ResourcePool.count event (qpeReadoutCircuit oracles t).eventCost =
      (t + 3 * t.choose 2) * (if .gate .singleQubit = event then 1 else 0) +
        (2 * t.choose 2 + 3 * (t / 2)) * (if .gate .cnot = event then 1 else 0) :=
  QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count oracles event t

/-- The complete dependency path retains every native inverse instruction. -/
public theorem qpeReadout_native_unit_depth (oracles : OracleModel) (t : Nat) :
    (qpeReadoutCircuit oracles t).evaluatedEventDepth (fun _ => 1) =
      t + 5 * t.choose 2 + 3 * (t / 2) :=
  QuantumFourierTransform.Native.qftNative_inverseCircuit_unit_depth oracles t

end

end QuantumAlg
