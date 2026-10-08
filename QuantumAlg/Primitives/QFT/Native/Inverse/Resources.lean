/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Primitives.QFT.Native.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Native event counts of the generated inverse QFT

The exact forward ledger is transported by the proved native-adjoint law.
Every count therefore belongs to the generated word itself.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

private theorem forwardPool (n : Nat) :
    (circuit .empty n).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.singleQubit) (n + 3 * n.choose 2) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.cnot) (2 * n.choose 2 + 3 * (n / 2)) := by
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (circuit .empty n).eventCost = _
  rw [qftNative_circuit_event_count]
  simp [ResourcePool.singleton, Multiset.count_replicate, eq_comm]

/-- Exact literal event counts of the actual generic adjoint of the native QFT word. -/
public theorem qftNative_inverseCircuit_event_count (oracles : OracleModel)
    (event : Resource.Event (.quantum AlgorithmGate.model oracles)) (n : Nat) :
    ResourcePool.count event (inverseCircuit oracles n).eventCost =
      (n + 3 * n.choose 2) * (if .gate .singleQubit = event then 1 else 0) +
        (2 * n.choose 2 + 3 * (n / 2)) * (if .gate .cnot = event then 1 else 0) := by
  rw [inverseCircuit, AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost, forwardPool]
  change Multiset.count event (Multiset.map (AlgorithmGate.oracleFreeEvent oracles)
    (ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit) (n + 3 * n.choose 2) +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot) (2 * n.choose 2 + 3 * (n / 2)))) = _
  simp [ResourcePool.singleton, Multiset.map_add, Multiset.map_replicate,
    AlgorithmGate.oracleFreeEvent, Multiset.count_replicate, eq_comm]

end

end QuantumAlg.QuantumFourierTransform.Native
