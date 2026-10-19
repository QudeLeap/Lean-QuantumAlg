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

public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Execution.Program
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Execution.Program

/-!
# Executable contract for a supplied QSP phase sequence

This execution interface is separate from the polynomial characterization.
Its independent target is the algebraic phase product [Lin22, hermfunc.tex:1103-1113].
-/

namespace QuantumAlg.ReflectionBasedQuantumSignalProcessing.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution.OwnedQubits Polynomial

variable (φ₀ : Real) (φs : List Real) (x : Real) (hx : x ∈ Set.Icc (-1 : Real) 1)

/-- Complete execution of a reflection-convention QSP word.

**Input.** One supplied owned qubit in any normalized joint state, arbitrary
external references, arbitrary real processing phases and x in [-1,1].
**Output.** The same qubit and the classical unit result. The exact algebraic
QSP product acts on the qubit, tensor the identity on every external reference.
**Resource budget.** With d = φs.length, exactly 2d + 1 native single-qubit gates
implement d signal factors and d + 1 exact Z processing rotations.
Unit-event depth is at most 2d + 1.
Resident and owned auxiliary space each count the same supplied qubit. No
new quantum systems or classical cells are allocated.
**Success.** Probability one and exact full-operator action.
**Source.** The product and characterization are [Lin22, hermfunc.tex:1103-1138].
-/
public def problem : Problem model (context 1) (context 1) .unit where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [StateRequirement.unitary (semanticOperator φ₀ φs x hx)]
  resources := { events := eventBudget φs.length, resident := space 1, auxiliary := space 1 }
  quantumTimeLimit := 2 * φs.length + 1

private lemma algorithm_solves :
    Algorithm.Solves (algorithm φ₀ φs x hx) (problem φ₀ φs x hx) := by
  constructor
  · intro environment _witness Reference input _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input _valid _initialized requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator φ₀ φs x hx) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds environment (semanticOperator φ₀ φs x hx)
      (program φ₀ φs x hx) (program_matrix φ₀ φs x hx environment.quantum)
      (Output.all (context 1) .unit) input
  · intro environment _witness Reference input _valid _initialized
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed environment rfl rfl
      (program φ₀ φs x hx) (Output.all (context 1) .unit) input
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact le_of_eq (actual_events φ₀ φs x hx path)
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_resident φ₀ φs x hx path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_auxiliary φ₀ φs x hx path
  · intro _environment _witness _Reference _input _valid _initialized _path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact le_of_eq (circuit_depth φ₀ φs x hx)

/-- Every supplied phase word has a complete execution meeting its independent contract. -/
public theorem main :
    ∃ candidate : Algorithm model (context 1) (context 1) .unit,
      candidate.Solves (problem φ₀ φs x hx) :=
  ⟨algorithm φ₀ φs x hx, algorithm_solves φ₀ φs x hx⟩

end

end QuantumAlg.ReflectionBasedQuantumSignalProcessing.Execution
