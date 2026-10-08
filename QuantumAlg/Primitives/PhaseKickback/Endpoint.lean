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

private def semanticOperator (f : Fin (2 ^ n) → Bool) :
    UnitaryOperator (context (n + 1)).register :=
  UnitaryOperator.reindex (basisEquiv (n + 1)).symm (xorOracleOp f)

/-- The native model explicitly grants the one source query used here. -/
public abbrev model (f : Fin (2 ^ n) → Bool) : ExecutionModel :=
  .quantum AlgorithmGate.model (XorOracle.model f)

private def program (f : Fin (2 ^ n) → Bool) :
    UnitaryCircuit AlgorithmGate.model (XorOracle.model f) (context (n + 1)).quantumLayout :=
  Execution.unitaryOfEqualWires (layout (n + 1)) (context (n + 1)).quantumLayout
    (layout_wires (n + 1)) (circuit f)

private theorem program_matrix (f : Fin (2 ^ n) → Bool) :
    (program f).matrix = semanticOperator f := by
  refine (Execution.unitaryOfEqualWires_matrix (layout (n + 1))
    (context (n + 1)).quantumLayout (layout_wires (n + 1)) (circuit f)).trans ?_
  refine (congrArg
    (UnitaryOperator.reindex (R := (layout (n + 1)).register)
      (S := (context (n + 1)).register)
      (Execution.basisOfEqualWires (layout (n + 1)) (context (n + 1)).quantumLayout
        (layout_wires (n + 1)))) (circuit_matrix f)).trans ?_
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

private def code (f : Fin (2 ^ n) → Bool) :
    Circuit (model f) (context (n + 1)) (context (n + 1)) :=
  .unitary (program f)

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
public def problem (f : Fin (2 ^ n) → Bool) :
    Problem (model f) (context (n + 1)) (context (n + 1)) .unit where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (semanticOperator f)]
  resources :=
    { events := ResourcePool.singleton (model := model f)
        (.oracle XorOracle.Coordinate.xor)
      resident := space (n + 1)
      auxiliary := space (n + 1) }
  depth :=
    { duration := fun _ => 1
      limit := 1
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- Execute the actual query and retain the complete supplied joint register. -/
public def algorithm (f : Fin (2 ^ n) → Bool) :
    Algorithm (model f) (context (n + 1)) (context (n + 1)) .unit where
  run := { code := code f, output := Output.all (context (n + 1)) .unit }

/-- Complete Output lists the same original owned systems. -/
private theorem output_listing (f : Fin (2 ^ n) → Bool) :
    (algorithm f).run.output.listing = (context (n + 1)).keys := rfl

/-- Complete Output keeps every supplied system. -/
public theorem algorithm_output_listing (f : Fin (2 ^ n) → Bool) :
    (algorithm f).run.output.listing = (context (n + 1)).keys := output_listing f

private theorem actual_events (f : Fin (2 ^ n) → Bool) (path : (code f).Path) :
    (code f).resourcePool path = (problem f).resources.events := by
  change ResourcePool.ofList (program f).eventTrace = _
  refine (UnitaryCircuit.ofList_eventTrace_eq_eventCost (program f)).trans ?_
  refine (Execution.unitaryOfEqualWires_cost (layout (n + 1))
    (context (n + 1)).quantumLayout (layout_wires (n + 1))
    (circuit f) .empty .empty).trans ?_
  exact circuit_events f

private theorem actual_resident (f : Fin (2 ^ n) → Bool) (path : (code f).Path) :
    (code f).peakResidentSpace path ≤ space (n + 1) := by
  intro axis
  change Nat.max ((context (n + 1)).residentSpace axis) 0 ≤ space (n + 1) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private theorem actual_auxiliary (f : Fin (2 ^ n) → Bool) (path : (code f).Path) :
    (code f).peakAuxiliarySpace path ≤ space (n + 1) := by
  intro axis
  change Nat.max ((context (n + 1)).auxiliarySpace axis) 0 ≤ space (n + 1) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private theorem algorithm_solves (f : Fin (2 ^ n) → Bool) :
    Algorithm.Solves (algorithm f) (problem f) := by
  constructor
  · intro Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid _initialization requirement present
    have same : requirement = StateRequirement.unitary (semanticOperator f) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (semanticOperator f)
      (program f) (program_matrix f)
      (Output.all (context (n + 1)) .unit) input
  · intro Reference input _valid _initialization
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed rfl rfl
      (program f) (Output.all (context (n + 1)) .unit) input
  · intro _Reference _input _valid _initialization path _supported
    exact le_of_eq (actual_events f path)
  · intro _Reference _input _valid _initialization path _supported
    exact actual_resident f path
  · intro _Reference _input _valid _initialization path _supported
    exact actual_auxiliary f path
  · intro _Reference _input _valid _initialization _path _supported
    exact circuit_depth f

/-- The actual complete query solves its independent execution problem and
preserves the original exact phase-kickback identity [dW19, qcnotes.tex:1145-1173]. -/
public theorem main (f : Fin (2 ^ n) → Bool) (x : Fin (2 ^ n)) :
    ∃ candidate, Algorithm.Solves candidate (problem f) ∧
    (xorOracleOp f).applyVec
        (((ket x : NormalizedVector (Qubits n)).tensor ketMinus :
          NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1)))
      = (if f x then (-1 : ℂ) else 1)
          • (((ket x : NormalizedVector (Qubits n)).tensor ketMinus :
              NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1))) := by
  exact ⟨algorithm f, algorithm_solves f, xor_action f x⟩

end

end QuantumAlg.PhaseKickback
