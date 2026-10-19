/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.Construction

/-!
# Actual one- and two-qubit counts of the Toffoli expansion

The same fifteen-gate native word contains exactly nine single-qubit gates
and six CNOTs. It contains no Toffoli token and no oracle invocation.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

/-- The complete event pool counts every phase, boundary Hadamard and parity CNOT. -/
lemma toffoliExpansion_eventCost (oracles : OracleModel) :
    (circuit oracles).eventCost =
      9 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
      6 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, toffoliExpansion_eventTrace]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero,
    show (9 : Nat) = 1 + 2 + 2 + 2 + 2 from rfl,
    show (6 : Nat) = 2 + 2 + 2 from rfl, add_nsmul, one_nsmul, two_nsmul]
  ac_rfl

/-- Exactly nine native single-qubit operations occur in the same expansion. -/
lemma toffoliExpansion_singleQubit_count (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate AlgorithmGate.Coordinate.singleQubit)
      (circuit oracles).eventCost = 9 := by
  rw [toffoliExpansion_eventCost]
  simp

/-- Exactly six native CNOT operations occur in the same expansion. -/
lemma toffoliExpansion_cnot_count (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate AlgorithmGate.Coordinate.cnot) (circuit oracles).eventCost = 6 := by
  rw [toffoliExpansion_eventCost]
  simp

/-- The expanded construction contains no residual native three-qubit gate. -/
lemma toffoliExpansion_toffoli_count (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate AlgorithmGate.Coordinate.toffoli)
      (circuit oracles).eventCost = 0 := by
  rw [toffoliExpansion_eventCost]
  simp

end
end QuantumAlg.Gate.Toffoli
