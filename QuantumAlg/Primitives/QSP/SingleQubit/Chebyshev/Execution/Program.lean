/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Construction
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Construction
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed

/-!
# Complete executions of reflection-convention phase words

The native circuit realizes the independently defined algebraic QSP operator,
including its action on arbitrary external references [Lin22, hermfunc.tex:1103-1138].
-/

namespace QuantumAlg.ReflectionBasedQuantumSignalProcessing.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution.OwnedQubits Polynomial

variable (φ₀ : Real) (φs : List Real) (x : Real) (hx : x ∈ Set.Icc (-1 : Real) 1)

private def semanticOperator : UnitaryOperator (context 1).register :=
  UnitaryOperator.reindex (basisEquiv 1).symm (operator φ₀ φs x hx)

private lemma supplied_wires : layout.wires = (context 1).quantumLayout.wires :=
  Execution.OwnedQubits.layout_wires 1

private def program :
    UnitaryCircuit AlgorithmGate.model .empty (context 1).quantumLayout :=
  Execution.unitaryOfEqualWires layout (context 1).quantumLayout supplied_wires
    (circuit φ₀ φs x hx)

private lemma program_matrix (environment : OracleModel.empty.Interpretation) :
    ((program φ₀ φs x hx).matrix environment) = semanticOperator φ₀ φs x hx := by
  unfold semanticOperator
  rw [← circuit_matrix φ₀ φs x hx environment]
  rw [program, Execution.unitaryOfEqualWires_matrix, UnitaryCircuit.binaryMatrix,
    UnitaryOperator.unitaryOperator_reindex_trans]
  apply congrArg (fun equivalence : layout.register.Index ≃ (context 1).register.Index =>
    UnitaryOperator.reindex equivalence ((circuit φ₀ φs x hx).matrix environment))
  apply Equiv.ext
  intro basis
  change (Execution.basisOfEqualWires layout (context 1).quantumLayout supplied_wires) basis =
    (Execution.basisOfEqualWires layout (context 1).quantumLayout supplied_wires)
      ((QuantumSignature.qubitsIndexEquiv 1).symm ((QuantumSignature.qubitsIndexEquiv 1) basis))
  rw [Equiv.symm_apply_apply]

private def code : Circuit model (context 1) (context 1) :=
  .unitary (program φ₀ φs x hx)

/-- Execute the actual processing word and retain its entire supplied register. -/
public def algorithm : Algorithm model (context 1) (context 1) .unit where
  run := { code := code φ₀ φs x hx, output := Output.all (context 1) .unit }

private lemma output_listing :
    (algorithm φ₀ φs x hx).run.output.listing = (context 1).keys := rfl

/-- The complete Output keeps the original qubit. -/
public lemma algorithm_output_listing :
    (algorithm φ₀ φs x hx).run.output.listing = (context 1).keys :=
  output_listing φ₀ φs x hx

private lemma actual_events (path : (code φ₀ φs x hx).Path) :
    (code φ₀ φs x hx).resourcePool path = eventBudget φs.length := by
  change ResourcePool.ofList (program φ₀ φs x hx).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost (program φ₀ φs x hx), program,
    Execution.unitaryOfEqualWires_cost, circuit_events]

/-- Exact expanded native gate multiplicities of every actual execution path. -/
public lemma algorithm_eventPool (path : (algorithm φ₀ φs x hx).run.code.Path) :
    (algorithm φ₀ φs x hx).run.code.resourcePool path = eventBudget φs.length :=
  actual_events φ₀ φs x hx path

private lemma actual_resident (path : (code φ₀ φs x hx).Path) :
    (code φ₀ φs x hx).peakResidentSpace path ≤ space 1 := by
  intro axis
  change Nat.max ((context 1).residentSpace axis) 0 ≤ space 1 axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_auxiliary (path : (code φ₀ φs x hx).Path) :
    (code φ₀ φs x hx).peakAuxiliarySpace path ≤ space 1 := by
  intro axis
  change Nat.max ((context 1).auxiliarySpace axis) 0 ≤ space 1 axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)


end

end QuantumAlg.ReflectionBasedQuantumSignalProcessing.Execution
