/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.Trotter.Circuit.Term
public import QuantumAlg.Primitives.Trotter.Circuit.Ordered
public import QuantumAlg.Primitives.Trotter.Circuit.Cost
public import QuantumAlg.Primitives.Trotter.Circuit.Grouped
public import QuantumAlg.Primitives.Trotter.Circuit.Blocks

public import QuantumAlg.Core.Algorithm.Unitary.Approximate.Owned
import all QuantumAlg.Core.Algorithm.Unitary.Approximate.Owned
import all QuantumAlg.Primitives.Trotter.Circuit.Cost
import all QuantumAlg.Primitives.Trotter.Circuit.Ordered

/-! # Exact native product-formula circuits and approximation contracts -/

namespace QuantumAlg.Trotter.SymmetricSimulation
noncomputable section

/-- **Input.** A positive number of supplied owned qubits, a real weighted Pauli
list `H`, nonnegative evolution time `t`, positive repetition count `r`, and
any normalized input jointly correlated with an external reference.
**Output.** All original systems after a unitary within
`t³ C₂(H) / (12r²)` of the independently specified `exp (-itH)` in full-phase
operator norm; the corresponding joint unitary-neighborhood state is required.
**Resource budget.** Writing `m` for list length, `a` for nonempty terms, `s`
for total support weight and `x,y` for total X/Y letters, the literal symmetric
word has `4r(s-a)` CNOTs and `2rm+4rx+12ry` one-qubit instructions. Their sum
bounds quantum time. Resident and auxiliary space each contain the supplied
`n` qubits, with no classical storage or fresh allocation.
**Success.** Probability one with the complete state requirement for every external reference.
**Source.** Symmetric product formula [CST+21, prelim.tex:30-35] and repeated
commutator bound [CST+21, prefactor.tex:105-114]; native Pauli rotations
[WBA11, h2.arxiv2.tex:384-412]. -/
public def problem {n : Nat} (_hn : 0 < n) (H : PauliSum n) (t : ℝ)
    (ht : 0 ≤ t) (r : Nat) (_hr : 0 < r) :
    Problem (.quantum AlgorithmGate.model .empty)
      (UnitaryExecution.Owned.context (nativeLayout n))
      (UnitaryExecution.Owned.context (nativeLayout n)) .unit :=
  UnitaryExecution.ApproximateOwned.problem
    (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm
      (timeEvolution H.toHamiltonian t))
    (secondError H t r) (secondError_nonneg H t ht r)
    (r • (2 • passPool H))
    (r * (4 * (weightSum H - activeCount H) + 2 * H.terms.length +
      4 * (letterSum H .x + letterSum H .y) + 8 * letterSum H .y))

/-- The retained native symmetric word solves the independent approximation problem. -/
public theorem main {n : Nat} (hn : 0 < n) (H : PauliSum n) (t : ℝ)
    (ht : 0 ≤ t) (r : Nat) (hr : 0 < r) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty)
      (UnitaryExecution.Owned.context (nativeLayout n))
      (UnitaryExecution.Owned.context (nativeLayout n)) .unit,
      candidate.Solves (problem hn H t ht r hr) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  refine ⟨UnitaryExecution.Owned.algorithm (second H t r), ?_⟩
  apply UnitaryExecution.ApproximateOwned.main
  · exact (secondRealization H t ht r hr).error_le
  · exact le_of_eq (by simp [second, secondStep_eventCost])
  · exact second_depth_le H t r

end
end QuantumAlg.Trotter.SymmetricSimulation
