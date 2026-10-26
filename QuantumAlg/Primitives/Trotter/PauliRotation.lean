/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.Trotter.PauliRotation.Construction
public import QuantumAlg.Core.Algorithm.Unitary.Owned
import all QuantumAlg.Primitives.Trotter.PauliRotation.Construction
import all QuantumAlg.Core.Algorithm.Unitary.Owned

/-!
# Complete exact Pauli-rotation execution

The retained native basis changes and parity passes implement the full Pauli
exponential. Empty support applies its scalar phase on an actual input qubit.
-/

namespace QuantumAlg.Trotter.PauliRotation

noncomputable section

/-- **Input.** A positive number `n` of supplied owned qubits, an arbitrary
normalized input with any external reference, a Pauli string `P`, and a real angle.
**Output.** All original qubits transformed by the exact operator `exp (-i θ P)`;
identity strings retain their full scalar phase at the operator boundary.
**Resource budget.** A nonempty support of weight `w` uses `2(w-1)` CNOTs and
`1 + 2x + 6y` one-qubit instructions, where `x,y` count X and Y letters.
Empty support uses one scalar one-qubit instruction. Quantum time is bounded
by that total instruction count. Resident and auxiliary space each contain the
same `n` dimension-two systems, with no classical storage or fresh allocation.
**Success.** Probability one and exact joint-state action with every external reference.
**Source.** Pauli exponentiation and basis changes [WBA11, h2.arxiv2.tex:384-412],
with the scalar phase retained before coherent control [WBA11, h2.arxiv2.tex:835]. -/
public def problem {n : Nat} (_hn : 0 < n) (P : PauliString n) (θ : ℝ) :
    Problem (.quantum AlgorithmGate.model .empty)
      (UnitaryExecution.Owned.context (nativeLayout n))
      (UnitaryExecution.Owned.context (nativeLayout n)) .unit :=
  UnitaryExecution.Owned.problem
    (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm
      (timeEvolution P.hamiltonian θ))
    (if P.support.Nonempty then
      (2 * (P.weight - 1)) • {.gate .cnot} + {.gate .singleQubit} +
      (2 * (pauliLetterCount P .x + pauliLetterCount P .y)) • {.gate .singleQubit} +
      (4 * pauliLetterCount P .y) • {.gate .singleQubit}
    else {.gate .singleQubit})
    (if P.support.Nonempty then 2 * (P.weight - 1) + 1 +
      2 * (pauliLetterCount P .x + pauliLetterCount P .y) + 4 * pauliLetterCount P .y
    else 1)

/-- The actual native construction solves the independent exact-rotation problem. -/
public theorem main {n : Nat} (hn : 0 < n) (P : PauliString n) (θ : ℝ) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty)
      (UnitaryExecution.Owned.context (nativeLayout n))
      (UnitaryExecution.Owned.context (nativeLayout n)) .unit,
      candidate.Solves (problem hn P θ) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  refine ⟨UnitaryExecution.Owned.algorithm (expPauli P θ), ?_⟩
  apply UnitaryExecution.Owned.main
  · exact NativeCircuit.matrix_eq_of_binaryOperator _ _ (expPauli_matrix P θ)
  · exact le_of_eq (expPauli_eventCost P θ)
  · exact expPauli_eventDepth_le P θ

end
end QuantumAlg.Trotter.PauliRotation
