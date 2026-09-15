/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.PhaseKickback.Construction
public import QuantumAlg.Core.Algorithm
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

/-!
# Complete eigenvalue phase kickback

The actual query has an independent full-operator target and a complete
supplied register. The original exact phase identity is retained alongside
the common execution contract.
-/

namespace QuantumAlg.GeneralizedPhaseKickback

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedQubits NormalizedVector

variable {n : Nat}

private def semanticOperator (U : UnitaryOperator (Qubits n)) :
    UnitaryOperator (context (1 + n)).register :=
  UnitaryOperator.reindex (basisEquiv (1 + n)).symm (UnitaryOperator.controlledQubits U)

private def program (U : UnitaryOperator (Qubits n)) :
    UnitaryCircuit (context (1 + n)).register :=
  UnitaryCircuit.reindex (basisEquiv (1 + n)).symm (circuit U)

private theorem program_matrix (U : UnitaryOperator (Qubits n)) :
    (program U).matrix = semanticOperator U := by
  exact (UnitaryCircuit.reindex_matrix (basisEquiv (1 + n)).symm (circuit U)).trans
    (congrArg (UnitaryOperator.reindex (basisEquiv (1 + n)).symm) (circuit_matrix U))

private theorem placement (U : UnitaryOperator (Qubits n)) :
    (program U).physical_idx = (context (1 + n)).physicalIdx := by
  change (circuit U).physical_idx = (context (1 + n)).physicalIdx
  rw [circuit_physicalIdx, ownedQubits_physicalIdx]

private def code (U : UnitaryOperator (Qubits n)) :
    Circuit (context (1 + n)) (context (1 + n)) :=
  .unitary (program U) (placement U)

/-- Complete controlled-unitary phase-kickback contract.

**Input.** A supplied owned 1 + n-qubit register in any normalized joint
state, with arbitrary external reference extensions. The controlled source-unitary query is supplied
by the source access model.
**Output.** Every original system remains live. The joint final state is the
exact controlled-unitary action tensor the identity on every reference. The
classical result is unit. The exact source phase identity additionally covers
every source eigenstate and arbitrary control amplitudes.
**Resource budget.** One controlled unitary query and unit-query depth at most one.
Resident and owned auxiliary space each count the same 1 + n supplied qubits.
No new quantum or classical storage is allocated.
**Success.** Probability one and exact full-operator action.
**Source.** The source query and its phase-kickback action are [CEMM98, cemm6.tex:140-166].
-/
public def problem (U : UnitaryOperator (Qubits n)) :
    Problem .quantum (context (1 + n)) (context (1 + n)) .unit where
  valid := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (semanticOperator U)]
  resources :=
    { events := ResourcePool.singleton (UnitarySource.controlledEvent n)
      resident := space (1 + n)
      auxiliary := space (1 + n) }
  depth := .quantum (fun _ => 1) 1

/-- Execute the actual query and retain the complete supplied joint register. -/
public def algorithm (U : UnitaryOperator (Qubits n)) :
    Algorithm .quantum (context (1 + n)) (context (1 + n)) .unit where
  run := { code := code U, output := Output.all (context (1 + n)) .unit }

/-- Complete Output lists the same original owned systems. -/
private theorem output_listing (U : UnitaryOperator (Qubits n)) :
    (algorithm U).run.output.listing = (context (1 + n)).keys := rfl

/-- Complete Output keeps every supplied system. -/
public theorem algorithm_output_listing (U : UnitaryOperator (Qubits n)) :
    (algorithm U).run.output.listing = (context (1 + n)).keys := output_listing U

private theorem actual_events (U : UnitaryOperator (Qubits n)) (path : (code U).Path) :
    (code U).resourcePool path = (problem U).resources.events := by
  change ResourcePool.ofList (program U).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, program,
    UnitaryCircuit.reindex_eventCost, circuit_events]
  rfl

private theorem actual_resident (U : UnitaryOperator (Qubits n)) (path : (code U).Path) :
    (code U).peakResidentSpace path ≤ space (1 + n) := by
  intro axis
  change Nat.max ((context (1 + n)).residentSpace axis) 0 ≤ space (1 + n) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (U : UnitaryOperator (Qubits n)) (path : (code U).Path) :
    (code U).peakAuxiliarySpace path ≤ space (1 + n) := by
  intro axis
  change Nat.max ((context (1 + n)).auxiliarySpace axis) 0 ≤ space (1 + n) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private theorem algorithm_solves (U : UnitaryOperator (Qubits n)) :
    Algorithm.Solves (algorithm U) (problem U) := by
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator U) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (semanticOperator U)
      (program U) (placement U) (program_matrix U)
      (Output.all (context (1 + n)) .unit) input
  · intro Reference input _valid
    exact Circuit.borrowedRestored_unitary_noBorrowed rfl rfl
      (program U) (placement U)
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact le_of_eq (actual_events U path)
  · intro _Reference _input _valid path _supported
    exact actual_resident U path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary U path
  · intro _Reference _input _valid _path _supported
    exact circuit_depth U

/-- The actual complete query solves its independent execution problem and
preserves the original exact phase-kickback identity [CEMM98, cemm6.tex:140-166]. -/
public theorem main (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp (θ * Complex.I) • (u : HilbertVector (Qubits n))) (a b : ℂ) :
    ∃ candidate, Algorithm.Solves candidate (problem U) ∧
    (UnitaryOperator.controlledQubits U).applyVec
        (HilbertVector.tensor
          ((a • ket0 + b • ket1 : HilbertVector (Qubits 1))) (u : HilbertVector (Qubits n)))
      =
      HilbertVector.tensor
        ((a • ket0 + (Complex.exp (θ * Complex.I) * b) • ket1 : HilbertVector (Qubits 1)))
        (u : HilbertVector (Qubits n)) := by
  exact ⟨algorithm U, algorithm_solves U, eigenvalue_action U u θ hu a b⟩

end

end QuantumAlg.GeneralizedPhaseKickback
