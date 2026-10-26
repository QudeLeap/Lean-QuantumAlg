/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.Trotter.Hubbard.Simulation
public import QuantumAlg.Core.Algorithm.Unitary.Approximate.Owned
import all QuantumAlg.Primitives.Trotter.Hubbard.Simulation
import all QuantumAlg.Primitives.Trotter.Hubbard.NativeCost
import all QuantumAlg.Primitives.Trotter.Hubbard.Blocks
import all QuantumAlg.Primitives.Trotter.Circuit.Blocks
import all QuantumAlg.Analysis.Trotter.Hubbard
import all QuantumAlg.Core.Algorithm.Unitary.Approximate.Owned

/-!
# Complete original-PLAQ Hubbard simulation

The actual native word retains every half-step, zero-angle term and chemical
scalar phase, and realizes the independent local error and resource contract.
-/

namespace QuantumAlg.FermiHubbard.PlaqSimulation
noncomputable section

/-- **Input.** An even periodic `L × L` lattice with `L ≥ 4`, real hopping,
interaction and chemical-potential parameters, nonnegative time, a positive
repetition count, and an arbitrary normalized state of the `2L²` supplied owned
qubits jointly correlated with any external reference.
**Output.** All original systems after an approximation to the full Hubbard
unitary, including the chemical shift. Its full-phase operator error is at most
`t³ L² (16|u||τ|²/3 + |u|²|τ|/6 + |τ|³) / r²`, with the corresponding complete
reference-aware unitary-neighborhood state requirement.
**Resource budget.** Exactly `r(32L(L-1)(L+1)+4L²)` CNOTs and `152rL²` native
one-qubit instructions; their sum bounds quantum time. Resident and auxiliary
space each contain the original `2L²` qubits, with no classical storage or
fresh allocation. No rotation synthesis or routing cost is asserted.
**Success.** Probability one for every admitted input and external reference.
**Source.** Symmetric commutator control [CST+21, prefactor.tex:105-114] applied
to the original complete I/P/G blocks; literal Pauli rotations
[WBA11, h2.arxiv2.tex:384-412] retain their scalar phase [WBA11, h2.arxiv2.tex:835]. -/
public def problem {L : Nat} (_hL : Even L) (_hsize : 4 ≤ L) (τ u μ t : ℝ)
    (ht : 0 ≤ t) (r : Nat) (_hr : 0 < r) :
    Problem (.quantum AlgorithmGate.model .empty)
      (UnitaryExecution.Owned.context (Trotter.nativeLayout (2 * L ^ 2)))
      (UnitaryExecution.Owned.context (Trotter.nativeLayout (2 * L ^ 2))) .unit :=
  UnitaryExecution.ApproximateOwned.problem
    (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (2 * L ^ 2)).symm
      (timeEvolution (hamiltonian L τ u μ) t))
    ((t ^ 3 / (r : ℝ) ^ 2) * localErrorCoefficient L τ u)
    (mul_nonneg (div_nonneg (pow_nonneg ht _) (sq_nonneg _))
      (localErrorCoefficient_nonneg L τ u))
    (r • (2 • nativePassPool L))
    (r * (32 * L * (L - 1) * (L + 1) + 156 * L ^ 2))

/-- The native original-PLAQ word solves the complete local-error simulation contract. -/
public theorem main {L : Nat} (hL : Even L) (hsize : 4 ≤ L) (τ u μ t : ℝ)
    (ht : 0 ≤ t) (r : Nat) (hr : 0 < r) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty)
      (UnitaryExecution.Owned.context (Trotter.nativeLayout (2 * L ^ 2)))
      (UnitaryExecution.Owned.context (Trotter.nativeLayout (2 * L ^ 2))) .unit,
      candidate.Solves (problem hL hsize τ u μ t ht r hr) := by
  let : NeZero L := ⟨by omega⟩
  refine ⟨UnitaryExecution.Owned.algorithm (trotterSecond L τ u μ t r), ?_⟩
  apply UnitaryExecution.ApproximateOwned.main
  · exact (trotterSecondLocalRealization hL hsize τ u μ t ht r hr).error_le
  · apply le_of_eq
    rw [trotterSecond, Trotter.secondBlocks_eventCost]
    simp only [plaqCircuits_eventCost]
    rw [plaqGroups_passPool hL, pauliSum_passPool (by omega)]
  · exact trotterSecond_depth_le hL hsize τ u μ t r

end
end QuantumAlg.FermiHubbard.PlaqSimulation
