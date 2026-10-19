/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Components.GateModel.Fourier
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Core.Algorithm.Unitary.Laws
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Trace

/-!
# Independent Fourier input, target state, and space specification

The target is the mathematical Fourier operator tensored with the identity
on every reference. Its supplied-register geometry and resource formulas do
not depend on the implementation program or its accounting projections.
-/

namespace QuantumAlg.QuantumFourierTransform

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Exact QFT uses native Hadamard, controlled-phase and SWAP instructions without oracle access. -/
public abbrev model : ExecutionModel := .quantum FourierGate.model .empty

private def qubitLayout (n : Nat) : QubitLayout n :=
  { physical_idx := Fin.val, physical_idx_injective := Fin.val_injective }

private def layout (n : Nat) : QuantumLayout n := (qubitLayout n).toQuantumLayout

/-- One supplied owned register occupying physical systems zero through n minus one. -/
@[reducible] public def inputContext (n : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ (layout n) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private lemma layout_wires_eq_context (n : Nat) :
    (layout n).wires = (inputContext n).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (layout n).wires = (layout n).wires ++ []
  exact (List.append_nil _).symm

/-- Big-endian binary encoding of the same physical wire values in the owned context. -/
public def inputBasisEquiv (n : Nat) : (inputContext n).register.Index ≃ (Qubits n).Index :=
  (Execution.basisOfEqualWires (layout n) (inputContext n).quantumLayout
    (layout_wires_eq_context n)).symm.trans (qubitLayout n).binaryIndexEquiv

/-- The Fourier operator written in the owned register's explicit coordinate basis. -/
public def semanticOperator (n : Nat) : UnitaryOperator (inputContext n).register :=
  UnitaryOperator.reindex (inputBasisEquiv n).symm (QFTOperator n)

/-- The independent Fourier transform acts jointly with identity on an arbitrary reference. -/
public def targetState (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    DensityOperator (Register.prod
      ((inputContext n).quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference (inputContext n).quantumLayout Finset.univ Reference
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (semanticOperator n) (1 : UnitaryOperator Reference))
      input.state.quantumMarginal)

private lemma targetState_normalized (n : Nat) (Reference : Register)
    (input : Execution.Input (inputContext n) Reference) :
    (targetState n Reference input).IsNormalized := by
  change (targetState n Reference input).mass = 1
  rw [targetState, DensityOperator.observeSelectionWithReference_mass,
    DensityOperator.applyUnitary_mass, ExecutionState.quantumMarginal_mass]
  exact input.normalized

/-- The complete owned output must satisfy the independent joint-reference Fourier target. -/
public def stateRequirement (n : Nat) : StateRequirement (inputContext n) (inputContext n) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (targetState n Reference input) (targetState_normalized n Reference input)

/-- The supplied bank accounts for exactly n dimension-two systems and no classical cells. -/
public def spaceBudget (n : Nat) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then n else 0

end

end QuantumAlg.QuantumFourierTransform
