/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Lowering.Resources
import all QuantumAlg.Primitives.QFT.Source.Resources
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-! # Exact standard-model counts of the lowered canonical QFT -/

namespace QuantumAlg.QuantumFourierTransform.Native
noncomputable section

/-- Every count is measured on the actual instruction refinement consumed by algorithms. -/
public lemma qftNative_circuit_event_count (oracles : OracleModel)
    (event : Resource.Event (.quantum AlgorithmGate.model oracles)) (n : Nat) :
    ResourcePool.count event (circuit oracles n).eventCost =
      (n + 3 * n.choose 2) * (if .gate .singleQubit = event then 1 else 0) +
        (2 * n.choose 2 + 3 * (n / 2)) * (if .gate .cnot = event then 1 else 0) := by
  rw [circuit, Lowering.lower_eventCost, Source.qftSource_circuit_eventCost]
  simp only [map_add, Lowering.expandedBudget_singleton_multiplicity,
    Lowering.replacementEvents, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton]
  split_ifs <;> ring

end
end QuantumAlg.QuantumFourierTransform.Native
