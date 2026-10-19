/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Execution.Selected
public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Execution.Context
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Execution.Results
import all QuantumAlg.Core.Algorithm.Unitary.Endpoint

/-!
# Complete unitary polynomial transformation

The source polynomial determines mathematical QPP phases before construction.
The actual native circuit realizes their complete operator on the original
input and one ancillary qubit. Its projected block is exactly the requested
Laurent polynomial, with the original exact resource counts retained in the
supporting construction [WZYW23, arxiv_v3.tex:635-666,2446-2465].
-/

namespace QuantumAlg.QSP.MultiQubit.QPP.Witness
noncomputable section

/-- **Input.** An n-qubit supplied data register, one owned ancilla, and granted
controlled access to U and its inverse; their joint state may have any external reference.
**Output.** Both registers after the complete mathematical QPP operator selected
from the bounded polynomial. Its zero-ancilla block equals the Laurent polynomial F(U).
**Resource budget.** 2 L controlled queries, 4 L+3 rotations, n+1 resident qubits,
one auxiliary qubit, no classical storage, and complete quantum time at most 6 L+3.
**Success.** Exact joint-state action with probability one; every live system is retained.
**Source.** Quantum phase evolution [WZYW23, arxiv_v3.tex:635-666,2446-2465]. -/
@[expose] public def problem (n L : Nat)
    (coeff : Fin (2 * L + 1) → ℂ) (source : TrigonometricPolynomialBound L coeff) :
    Problem (.quantum AlgorithmGate.model (QPPOracle.model n))
      (Execution.context n) (Execution.context n) .unit where
  Witness := UnitaryOperator (Qubits n)
  valid := fun environment U _ => environment.quantum = QPPOracle.interpretation U
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ U => [StateRequirement.unitary (Execution.physicalTarget (Execution.target U
    source))]
  resources := Execution.resources n L
  quantumTimeLimit := 6 * L + 3

/-- The complete native QPP execution solves the independent polynomial-transformation problem. -/
public theorem main (n L : Nat)
    (coeff : Fin (2 * L + 1) → ℂ) (source : TrigonometricPolynomialBound L coeff) :
    ∃ candidate : Algorithm _ _ _ .unit, candidate.Solves (problem n L coeff source) := by
  refine ⟨Execution.algorithm n source, ?_⟩
  have actual := Execution.qpp_complete_execution n source
  constructor
  · intro environment witness Reference input _valid _initialized
    exact actual.success environment () Reference input trivial trivial
  · intro environment witness Reference input valid _initialized requirement present
    apply actual.states environment () Reference input trivial trivial requirement
    change requirement ∈ [StateRequirement.unitary
      ((Execution.program n source).matrix environment.quantum)]
    change environment.quantum = QPPOracle.interpretation witness at valid
    rw [valid, Execution.program_matrix witness source]
    exact present
  · intro environment witness Reference input _valid _initialized
    exact actual.borrowed environment () Reference input trivial trivial
  · intro environment witness Reference input _valid _initialized
    exact actual.events environment () Reference input trivial trivial
  · intro environment witness Reference input _valid _initialized
    exact actual.resident environment () Reference input trivial trivial
  · intro environment witness Reference input _valid _initialized
    exact actual.auxiliary environment () Reference input trivial trivial
  · intro environment witness Reference input _valid _initialized
    exact actual.time environment () Reference input trivial trivial

end
end QuantumAlg.QSP.MultiQubit.QPP.Witness
