/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.PhaseKickback.Endpoint.Execution
import all QuantumAlg.Primitives.PhaseKickback.Endpoint.Execution

public import QuantumAlg.Primitives.PhaseKickback.Construction
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Algorithm.Unitary.Requirement
public import QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.PhaseKickback.Construction
import all QuantumAlg.Primitives.PhaseKickback.Basic
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed

/-!
# Complete XOR-oracle phase kickback

The actual query has an independent full-operator target and a complete
supplied register. The original exact phase identity is retained alongside
the common execution contract.
-/

namespace QuantumAlg.PhaseKickback

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits NormalizedVector

variable {n : Nat}

/-- Complete XOR-oracle phase-kickback contract.

**Input.** A supplied owned n + 1-qubit register in any normalized joint
state, with arbitrary external reference extensions. The XOR-oracle query is supplied
by the source access model.
**Output.** Every original system remains live. The joint final state is the
exact XOR-oracle action tensor the identity on every reference. The
classical result is unit. The exact source phase identity additionally covers
every input basis value with a minus-state target.
**Resource budget.** One XOR-oracle query and unit-query depth at most one.
Resident and owned auxiliary space each count the same n + 1 supplied qubits.
No new quantum or classical storage is allocated.
**Success.** Probability one and exact full-operator action.
**Source.** The source query and its phase-kickback action are [dW19, qcnotes.tex:1145-1173].
-/
@[expose] public def problem (n : Nat) :
    Problem (model n) (context (n + 1)) (context (n + 1)) .unit where
  Witness := Fin (2 ^ n) → Bool
  valid := fun environment f _ => environment.quantum = XorOracle.interpretation f
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ f => [StateRequirement.unitary (semanticOperator f)]
  resources :=
    { events := ResourcePool.singleton (model := model n)
        (.oracle XorOracle.Coordinate.xor)
      resident := space (n + 1)
      auxiliary := space (n + 1) }
  quantumTimeLimit := 1

private lemma algorithm_solves (n : Nat) :
    Algorithm.Solves (algorithm n) (problem n) := by
  constructor
  · intro environment f Reference input admitted _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment f Reference input admitted _initialization requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator f) :=
      List.mem_singleton.mp present
    subst requirement
    apply StateRequirement.unitary_holds environment (semanticOperator f)
      (program n) ?_
      (Output.all (context (n + 1)) .unit) input
    change environment.quantum = XorOracle.interpretation f at admitted
    rw [admitted]
    exact program_matrix f
  · intro environment f Reference input admitted _initialization
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed environment rfl rfl
      (program n) (Output.all (context (n + 1)) .unit) input
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact le_of_eq (actual_events n path)
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact actual_resident n path
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact actual_auxiliary n path
  · intro _environment _witness _Reference _input _valid _initialization _path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact circuit_depth n

/-- The actual complete query solves the independent phase-kickback problem. -/
public theorem main (n : Nat) :
    ∃ candidate : Algorithm (model n) (context (n + 1)) (context (n + 1)) .unit,
      Algorithm.Solves candidate (problem n) :=
  ⟨algorithm n, algorithm_solves n⟩

end

end QuantumAlg.PhaseKickback
