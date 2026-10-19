/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Construction
public import QuantumAlg.Core.Algorithm.Unitary.Endpoint
public import QuantumAlg.Core.Execution.Supplied.Qubits
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Construction
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Supplied.Qubits
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Actual supplied and auxiliary physical registers for ECADD

The raw product encoding places the control and mutable x/y coordinates first.
These 1+2f systems are supplied and mutable. The remaining systems are owned
auxiliary storage. Equal ordered wire lists identify the original canonical
program and this role-aware context; no arbitrary unitary changes coordinates.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ControlledPointAddition.Execution
noncomputable section

open QuantumAlg.Execution

/-- Native algorithm-gate model for controlled point addition. -/
public abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty

private def auxiliaryContext (f : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨1⟩
    (OwnedQubitPrefix.inputLayout (1 + 2 * f) (auxiliaryQubitCount f)).toQuantumLayout
    (by decide) (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

/-- Supplied control/data prefix followed by precisely the owned arithmetic/selector suffix. -/
@[reducible] public def context (f : Nat) : RuntimeCtx .quantum :=
  (auxiliaryContext f).addSuppliedLayout ⟨0⟩
    (OwnedQubitPrefix.prefixLayout (1 + 2 * f)).toQuantumLayout
    (by change (⟨0⟩ : StorageKey) ∉ [⟨1⟩]; decide)
    (OwnedQubitPrefix.prefix_disjoint (1 + 2 * f) (auxiliaryQubitCount f))

lemma context_wires (f : Nat) :
    (QubitLayout.canonical (logicalQubitCount f)).toQuantum.wires =
      (context f).quantumLayout.wires := by
  rw [logicalQubitCount_eq_public_add_auxiliary]
  exact OwnedQubitPrefix.post_canonical_wires (1 + 2 * f) (auxiliaryQubitCount f)

public lemma context_resident (f : Nat) :
    (context f).residentSpace = SuppliedQubits.space (logicalQubitCount f) := by
  simp only [context, auxiliaryContext, RuntimeCtx.residentSpace_addSuppliedLayout,
    RuntimeCtx.residentSpace_addOwnedLayout, RuntimeCtx.residentSpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change (OwnedQubitPrefix.prefixLayout (1 + 2 * f)).toQuantumLayout.dimensionCount dimension +
        (OwnedQubitPrefix.inputLayout (1 + 2 * f) (auxiliaryQubitCount
          f)).toQuantumLayout.dimensionCount dimension =
          if (2 : ℕ+) = dimension then logicalQubitCount f else 0
      rw [QubitLayout.toQuantumLayout_dimensionCount, QubitLayout.toQuantumLayout_dimensionCount,
        logicalQubitCount_eq_public_add_auxiliary]
      split <;> simp

public lemma context_auxiliary (f : Nat) :
    (context f).auxiliarySpace = SuppliedQubits.space (auxiliaryQubitCount f) := by
  simp only [context, auxiliaryContext, RuntimeCtx.auxiliarySpace_addSuppliedLayout,
    RuntimeCtx.auxiliarySpace_addOwnedLayout, RuntimeCtx.auxiliarySpace_empty, add_zero]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (OwnedQubitPrefix.inputLayout (1 + 2 * f) (auxiliaryQubitCount
        f)).toQuantumLayout_dimensionCount dimension

variable [params : Arithmetic.VariableModularMul.Parameters]

abbrev rawLayout := (QubitLayout.canonical
  GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width).toQuantum

lemma raw_wires : (rawLayout (params := params)).wires = (context
  params.width).quantumLayout.wires := by
  rw [show (rawLayout (params := params)).wires =
    (QubitLayout.canonical (logicalQubitCount params.width)).toQuantum.wires from
      congrArg (fun n => (QubitLayout.canonical n).toQuantum.wires) program_width_exact]
  exact context_wires params.width

/-- Only matching values on the same ordered physical wires change representation. -/
def rawBasis : (rawLayout (params := params)).Basis ≃ (context params.width).register.Index :=
  QuantumAlg.Execution.basisOfEqualWires rawLayout (context params.width).quantumLayout raw_wires

end
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ControlledPointAddition.Execution
