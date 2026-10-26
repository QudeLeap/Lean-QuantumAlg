/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.FTQC.Toffoli7T.Realization
public import QuantumAlg.Core.Algorithm.Unitary.Owned
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Realization
import all QuantumAlg.Core.Algorithm.Unitary.Owned

/-! # Complete strict-model execution of the seven-T Toffoli -/

namespace QuantumAlg.FTQC.Toffoli7T

noncomputable section

/--
**Input.**
- Any joint state of three owned qubits, including entanglement with an external reference.

**Output.**
- The same three qubits after exact Toffoli, with controls zero and one and target two.

**Resource budget.**
- Seven T, six CNOT, two H and nine S instructions; depth at most eighteen.
- Resident and auxiliary space each include the three supplied owned qubits.
- No fresh qubits, additional workspace or classical storage.

**Success.**
- Exact full-state action with probability one, including the external reference.

**Source.**
- Nielsen and Chuang, Quantum Computation and Quantum Information,
  Chapter 4, Section 4.3, Figure 4.9 (citation-only book credit).
- Each adjoint T is expanded to one T followed by three S instructions.
-/
public def problem :=
  UnitaryExecution.Owned.problem
    (oracles := OracleModel.empty) (fun _ => toffoliPhysicalOp)
    (toffoli7TEvents OracleModel.empty) 18

/-- A strict Clifford+T algorithm solves the independent complete-state Toffoli problem. -/
public theorem main :
    ∃ implementation, Algorithm.Solves (allowAllocation := true) implementation problem := by
  refine ⟨UnitaryExecution.Owned.algorithm (toffoli7TCircuit OracleModel.empty), ?_⟩
  exact UnitaryExecution.Owned.main (fun _ => toffoliPhysicalOp)
    (toffoli7TEvents OracleModel.empty) 18 (toffoli7TCircuit OracleModel.empty)
    (toffoli7T OracleModel.empty).matrix_eq
    (le_of_eq (toffoli7T_eventCost OracleModel.empty))
    (le_of_eq (toffoli7T_eventDepth OracleModel.empty))

end

end QuantumAlg.FTQC.Toffoli7T
