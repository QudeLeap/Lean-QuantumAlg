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
public lemma orderFinding_nativeSourceFamilyCounts (t width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (sourceModel t width))
        (.gate .singleQubit) (initialLayer t width).eventCost +
      (readoutLayer t width).macroCount "hadamard" = 2 * t ∧
    (readoutLayer t width).macroCount "controlled-phase" = t.choose 2 ∧
    (readoutLayer t width).macroCount "swap" = t / 2 := by
  have initial : ResourcePool.count
      (model := .quantum AlgorithmGate.model (sourceModel t width))
      (.gate .singleQubit) (initialLayer t width).eventCost = t := by
    rw [initialLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
      Gate.HadamardLayer.hadamardLayer_circuit_eventCost (sourceModel t width) t]
    simp
  have readout (name : String) : (readoutLayer t width).macroCount name =
      t * (if "hadamard" = name then 1 else 0) +
        t.choose 2 * (if "controlled-phase" = name then 1 else 0) +
          (t / 2) * (if "swap" = name then 1 else 0) := by
    rw [readoutLayer, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_macroCount]
    exact QuantumFourierTransform.Native.qftNative_inverseCircuit_macro_count
      (sourceModel t width) name t
  simp [initial, readout]
  omega

end

end QuantumAlg.OrderFinding.Native
