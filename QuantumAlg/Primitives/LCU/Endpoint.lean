/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.LCU.Endpoint.Execution
import all QuantumAlg.Primitives.LCU.Endpoint.Execution

public import QuantumAlg.Primitives.LCU.Construction
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Algorithm.Unitary.Requirement
public import QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.LCU.Construction
import all QuantumAlg.Primitives.LCU.Basic
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Oracle.LCU
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed

/-!
# Complete LCU execution and the original exact projected block

The same placed three-query circuit implements the source LCU operator,
retains the complete supplied input and obeys independent native budgets
[Lin22, hermfunc.tex:531-554]. Its exact projected block keeps the original
nonnegative-coefficient domain, including zero coefficients with positive sum.
-/

namespace QuantumAlg.LinearCombinationOfUnitaries

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits

variable {a n : Nat}

/-- Independent complete LCU execution contract.

**Input.** A supplied owned a+n-qubit register in any normalized joint state,
with every external reference extension admitted. Query access supplies the
a-qubit preparation unitary V, its inverse, and the controlled SELECT family.
**Output.** The entire register remains live after the exact unitary
W=(V dagger tensor I) SELECT (V tensor I). The joint-state target includes
the identity on every reference. The classical result is unit.
**Resource budget.** One forward preparation query, one inverse preparation query
and one SELECT query suffice, each at its own coordinate. Unit-query depth is at most three.
Resident and
owned auxiliary space are both a+n qubits, describing the same supplied
systems. No new qubits, classical cells or other dimensions are allocated.
**Success.** Probability one with the exact full operator action. When V
prepares the normalized square-root coefficients, the zero-control block is
the coefficient-weighted unitary sum divided by the coefficient sum.
**Source.** The LCU lemma and its preparation/SELECT access model are
[Lin22, hermfunc.tex:531-554]. The statement does not assert a gate synthesis
cost or a successful postselection probability for arbitrary input states.
-/
@[expose] public def problem (a n : Nat) :
    Problem (model a n) (context (a + n)) (context (a + n)) .unit where
  Witness := UnitaryOperator (Qubits a) × (Fin (2 ^ a) → UnitaryOperator (Qubits n))
  valid := fun environment witness _ =>
    environment.quantum = LCUOracle.interpretation witness.1 witness.2
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ witness => [StateRequirement.unitary (semanticOperator witness.1 witness.2)]
  resources :=
    { events := ResourcePool.singleton (model := model a n) (.oracle .prepare) +
        ResourcePool.singleton (model := model a n) (.oracle .select) +
        ResourcePool.singleton (model := model a n) (.oracle .unprepare)
      resident := space (a + n)
      auxiliary := space (a + n) }
  quantumTimeLimit := 3

private lemma algorithm_solves (a n : Nat) :
    Algorithm.Solves (algorithm a n) (problem a n) := by
  constructor
  · intro environment witness Reference input admitted _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment witness Reference input admitted _initialization requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator witness.1 witness.2) :=
      List.mem_singleton.mp present
    subst requirement
    apply StateRequirement.unitary_holds environment (semanticOperator witness.1 witness.2)
      (program a n) ?_
      (Output.all (context (a + n)) .unit) input
    change environment.quantum = LCUOracle.interpretation witness.1 witness.2 at admitted
    rw [admitted]
    exact program_matrix witness.1 witness.2
  · intro environment witness Reference input admitted _initialization
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed environment rfl rfl
      (program a n) (Output.all (context (a + n)) .unit) input
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact le_of_eq (actual_events a n path)
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact actual_resident a n path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact actual_auxiliary a n path
  · intro _environment _witness _Reference _input _valid _initialization _path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact le_of_eq (circuit_depth a n)

/-- The actual LCU circuit solves the independent complete operator problem. -/
public theorem main (a n : Nat) :
    ∃ candidate : Algorithm (model a n) (context (a + n)) (context (a + n)) .unit,
      Algorithm.Solves candidate (problem a n) :=
  ⟨algorithm a n, algorithm_solves a n⟩

end

end QuantumAlg.LinearCombinationOfUnitaries
