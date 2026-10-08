/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Native
import all QuantumAlg.Algorithms.OrderFinding.Native
import all QuantumAlg.Primitives.QFT.Native.Inverse.Macros
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Source-family observations on the actual native order-finding layers

The first layer consists solely of its explicit parallel Hadamards. The
readout layer retains the inverse QFT's Hadamard, controlled-phase and SWAP
occurrences on their actual expanded native word. These descriptive source
counts do not replace the same circuit's native event accounting
[Sho95, source.tex:1183-1185] [dW19, qcnotes.tex:2203-2225].
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

/-- The original source families count the actual initial and readout layers:
explicit initial Hadamards plus Fourier Hadamards, phases and register swaps. -/
public theorem orderFinding_nativeSourceFamilyCounts {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (sourceModel access))
        (.gate .singleQubit) (initialLayer access).eventCost +
      (readoutLayer access).macroCount "hadamard" = 2 * t ∧
    (readoutLayer access).macroCount "controlled-phase" = t.choose 2 ∧
    (readoutLayer access).macroCount "swap" = t / 2 := by
  have initial : ResourcePool.count
      (model := .quantum AlgorithmGate.model (sourceModel access))
      (.gate .singleQubit) (initialLayer access).eventCost = t := by
    rw [initialLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
      Gate.HadamardLayer.hadamardLayer_circuit_eventCost (sourceModel access) t]
    simp
  have readout (name : String) : (readoutLayer access).macroCount name =
      t * (if "hadamard" = name then 1 else 0) +
        t.choose 2 * (if "controlled-phase" = name then 1 else 0) +
          (t / 2) * (if "swap" = name then 1 else 0) := by
    rw [readoutLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_macroCount]
    exact QuantumFourierTransform.Native.qftNative_inverseCircuit_macro_count
      (sourceModel access) name t
  simp [initial, readout]
  omega

end

end QuantumAlg.OrderFinding.Native
