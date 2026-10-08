/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.Refinement.Counts
import all QuantumAlg.Components.Gates.Toffoli.Refinement
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# One- and two-qubit operation bounds for exact Toffoli substitution

The bound charges only actual native gate occurrences. Oracle queries remain
separate. Each Toffoli contributes fifteen native gates and requires no new wire.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

/-- Count the three distinct native gate coordinates, excluding all query coordinates. -/
def nativeGateCount {oracles : OracleModel}
    (pool : ResourcePool (.quantum AlgorithmGate.model oracles)) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit) pool +
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) pool +
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli) pool

/-- Native gate counts add across literal event pools. -/
theorem nativeGateCount_add {oracles : OracleModel}
    (left right : ResourcePool (.quantum AlgorithmGate.model oracles)) :
    nativeGateCount (left + right) = nativeGateCount left + nativeGateCount right := by
  simp only [nativeGateCount, ResourcePool.count_add]
  omega

/-- Repeating a native event pool repeats all of its native gate counts. -/
theorem nativeGateCount_nsmul {oracles : OracleModel} (repetitions : Nat)
    (pool : ResourcePool (.quantum AlgorithmGate.model oracles)) :
    nativeGateCount (repetitions • pool) = repetitions * nativeGateCount pool := by
  simp only [nativeGateCount, ResourcePool.count_nsmul, Nat.mul_add]

/-- Each actual default-model native gate contributes one to the gate total. -/
theorem nativeGateCount_singleton_gate {oracles : OracleModel}
    (coordinate : AlgorithmGate.Coordinate) :
    nativeGateCount (ResourcePool.singleton
      (model := .quantum AlgorithmGate.model oracles) (.gate coordinate)) = 1 := by
  cases coordinate <;> simp [nativeGateCount]

/-- Queries are kept separate from native gate totals. -/
theorem nativeGateCount_singleton_query {oracles : OracleModel}
    (coordinate : oracles.Coordinate) :
    nativeGateCount (ResourcePool.singleton
      (model := .quantum AlgorithmGate.model oracles) (.oracle coordinate)) = 0 := by
  simp [nativeGateCount]

/-- The actual one- and two-qubit count is at most fifteen times the source native gate count. -/
theorem toffoliExpansion_native_gate_bound {oracles : OracleModel} {count : Nat}
    {ambient : QuantumLayout count} (source : UnitaryCircuit AlgorithmGate.model oracles ambient) :
    nativeGateCount (expand source).eventCost ≤ 15 * nativeGateCount source.eventCost := by
  unfold nativeGateCount
  rw [toffoliExpansion_expanded_singleQubit_count, toffoliExpansion_expanded_cnot_count,
    toffoliExpansion_expanded_toffoli_count]
  omega

end
end QuantumAlg.Gate.Toffoli
