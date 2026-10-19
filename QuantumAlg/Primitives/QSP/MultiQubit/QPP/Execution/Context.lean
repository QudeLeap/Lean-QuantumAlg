/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Endpoint
public import QuantumAlg.Components.Oracle.QPP
public import QuantumAlg.Core.Execution.Supplied.Qubits
import all QuantumAlg.Core.Algorithm.Unitary.Endpoint
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Supplied.Qubits
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# QPP input ownership and independent resource limits

The original n data qubits form a supplied mutable interface. Only the leading
signal qubit is owned auxiliary storage. All systems remain in the complete
joint output, with no purity assumption on their input or external reference.
The source uses 2L controlled queries and 4L+3 rotations
[WZYW23, arxiv_v3.tex:598-618,650-666].
-/

namespace QuantumAlg.QSP.MultiQubit.QPP.Execution
noncomputable section

open QuantumAlg.Execution

private def dataContext (n : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addSuppliedLayout ⟨1⟩ (OwnedQubitPrefix.inputLayout 1 n).toQuantumLayout
    (by decide) (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

/-- One owned ancilla and n supplied data qubits, in their original physical order. -/
@[reducible] public def context (n : Nat) : RuntimeCtx .quantum :=
  (dataContext n).addOwnedLayout ⟨0⟩ (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout
    (by change (⟨0⟩ : StorageKey) ∉ [⟨1⟩]; decide)
    (OwnedQubitPrefix.prefix_disjoint 1 n)

lemma context_wires (n : Nat) :
    (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout.wires =
      (context n).quantumLayout.wires := by
  exact OwnedQubitPrefix.post_canonical_wires 1 n

/-- The complete mathematical binary operator on the same ordered physical systems. -/
public def physicalTarget {n : Nat} (operator : UnitaryOperator (Qubits (1 + n))) :
    UnitaryOperator (context n).register :=
  UnitaryOperator.reindex
    (QuantumAlg.Execution.basisOfEqualWires
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout
      (context n).quantumLayout (context_wires n))
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + n)).symm operator)

/-- Degree-indexed native query and rotation multiplicities, independent of an execution. -/
@[expose] public def events (n : Nat) (L : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (QPPOracle.model n)) :=
  (2 * L) • ResourcePool.singleton (QPPOracle.event n) +
    (4 * L + 3) • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (QPPOracle.model n)) (.gate .singleQubit)

/-- n+1 resident qubits and exactly one auxiliary qubit, with no classical storage. -/
@[expose] public def resources (n : Nat) (L : Nat) :
    ResourceBudget (.quantum AlgorithmGate.model (QPPOracle.model n)) where
  events := events n L
  resident := fun axis => match axis with
    | .classicalBits => 0
    | .quantumSystems dimension => if (2 : ℕ+) = dimension then 1 + n else 0
  auxiliary := fun axis => match axis with
    | .classicalBits => 0
    | .quantumSystems dimension => if (2 : ℕ+) = dimension then 1 else 0

lemma context_resident (n : Nat) :
    (context n).residentSpace = SuppliedQubits.space (1 + n) := by
  simp only [context, dataContext, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_addSuppliedLayout, RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout.dimensionCount dimension +
        (OwnedQubitPrefix.inputLayout 1 n).toQuantumLayout.dimensionCount dimension =
          if (2 : ℕ+) = dimension then 1 + n else 0
      rw [QubitLayout.toQuantumLayout_dimensionCount,
        QubitLayout.toQuantumLayout_dimensionCount]
      split <;> simp

lemma context_auxiliary (n : Nat) :
    (context n).auxiliarySpace = SuppliedQubits.space 1 := by
  simp only [context, dataContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_addSuppliedLayout, RuntimeCtx.auxiliarySpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout_dimensionCount dimension

end
end QuantumAlg.QSP.MultiQubit.QPP.Execution
