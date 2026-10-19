/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
public import QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Semantics
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Semantics
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Resources

/-!
# Complete three-word native variable modular multiplication

The independent arithmetic operator, complete Output, all native events,
space and depth describe the same actual coherent bit-pair program. Both
quantum inputs remain present and unchanged. Every mixed or coherent input
and its arbitrary external reference are covered by the full-state equation.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney

noncomputable section

open Execution.OwnedQubits

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma supplied_wires (width : Nat) :
    (QubitLayout.canonical (encoding width).width).toQuantum.wires =
      (context (3 * width)).quantumLayout.wires := by
  rw [(variableGidney_interface width).1]
  exact Execution.OwnedQubits.canonical_wires (3 * width)

private def nativeOperator (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryOperator (context (3 * width)).register :=
  UnitaryOperator.reindex
    (Execution.basisOfEqualWires
      (QubitLayout.canonical (encoding width).width).toQuantum
      (context (3 * width)).quantumLayout (supplied_wires width))
    (UnitaryOperator.reindex
      (QubitLayout.canonical (encoding width).width).basisEquiv.symm
      (wordVariableOperator width modulus))

private def nativeProgram (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (context (3 * width)).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QubitLayout.canonical (encoding width).width).toQuantum
    (context (3 * width)).quantumLayout (supplied_wires width)
      (program width modulus)

private lemma native_matrix {environment : OracleModel.empty.Interpretation}
    (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (nativeProgram width modulus).matrix environment = nativeOperator width modulus := by
  unfold nativeOperator
  have sourceMatrix : (program width modulus).matrix environment =
      UnitaryOperator.reindex
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm
          (wordVariableOperator width modulus) := by
    have binary := congrArg
      (UnitaryOperator.reindex
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm)
      (variableGidney_matrix (environment := environment) width modulus)
    change UnitaryOperator.reindex
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm
          (UnitaryOperator.reindex
            (QubitLayout.canonical (encoding width).width).basisEquiv
            ((program width modulus).matrix environment)) = _ at binary
    rw [UnitaryOperator.unitaryOperator_reindex_cancel] at binary
    exact binary
  rw [nativeProgram, Execution.unitaryOfEqualWires_matrix, sourceMatrix]

private def code (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (context (3 * width)) (context (3 * width)) :=
  .unitary (nativeProgram width modulus)

/-- Independent complete variable-product execution contract.

**Input.** Three supplied owned width-qubit words in any normalized joint
state, including mixed states and correlations with an arbitrary reference.
The fitted modulus is a compilation parameter. Neither quantum input is
required to be nonzero or invertible; the modulus need not be odd.

**Output.** All three words remain live. On canonical target labels z<N,
the exact arithmetic action is (x,y,z) to (x,y,(z+x*y) mod N). Noncanonical
target labels are fixed. The full independent permutation acts jointly
with the reference identity, preserving every relative phase.

**Resource budget.** Each default-model gate coordinate is bounded by
width*stageEventBound(width), where the stage cap is four times the inner
MAC gate bound. This charges every literal gate-local control expansion.
Resident and owned auxiliary pools
both contain the three supplied words, exactly 3*width dimension-two
systems. The run allocates no other quantum or classical storage.

**Success.** The unit result has probability one; the full-state target
holds for every input. Width zero is the empty, zero-event instance.

**Source.** Binary controlled additions [VBE95, 9511018.tex:333-367],
instantiated with exact pivot-flip offsets [G17, paper.tex:319-334].
-/
public def problem (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    Problem (.quantum AlgorithmGate.model .empty)
      (context (3 * width)) (context (3 * width)) .unit where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => [StateRequirement.unitary (nativeOperator width modulus)]
  resources :=
    { events := nativeBudget width
      resident := space (3 * width)
      auxiliary := space (3 * width) }
  quantumTimeLimit := eventBound width

/-- Execute the actual three-word circuit and retain its complete output. -/
public def algorithm (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    Algorithm (.quantum AlgorithmGate.model .empty)
      (context (3 * width)) (context (3 * width)) .unit where
  run := { code := code width modulus, output := Output.all (context (3 * width)) .unit }

private lemma actual_events (width : Nat) (modulus : Fin (2 ^ width + 1))
    (path : (code width modulus).Path) :
    (code width modulus).resourcePool path ≤ nativeBudget width := by
  change ResourcePool.ofList (nativeProgram width modulus).eventTrace ≤ nativeBudget width
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  have cost : (nativeProgram width modulus).eventCost =
      (program width modulus).eventCost :=
    Execution.unitaryOfEqualWires_cost
      (QubitLayout.canonical (encoding width).width).toQuantum
      (context (3 * width)).quantumLayout (supplied_wires width)
      (program width modulus) .empty .empty
  rw [cost]
  exact variableGidney_native_budget width modulus

private lemma actual_resident (width : Nat) (modulus : Fin (2 ^ width + 1))
    (path : (code width modulus).Path) :
    (code width modulus).peakResidentSpace path ≤ space (3 * width) := by
  intro axis
  change Nat.max ((context (3 * width)).residentSpace axis) 0 ≤ space (3 * width) axis
  rw [ownedQubits_resident]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_auxiliary (width : Nat) (modulus : Fin (2 ^ width + 1))
    (path : (code width modulus).Path) :
    (code width modulus).peakAuxiliarySpace path ≤ space (3 * width) := by
  intro axis
  change Nat.max ((context (3 * width)).auxiliarySpace axis) 0 ≤ space (3 * width) axis
  rw [ownedQubits_auxiliary]
  exact le_of_eq (Nat.max_zero _)

private lemma actual_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (path : (code width modulus).Path) :
    (code width modulus).depth (fun _ => 1) path ≤ eventBound width := by
  change DepthExpr.depthEval (fun _ => 1)
    ((nativeProgram width modulus).eventDepth .empty .empty) ≤ _
  rw [nativeProgram, Execution.unitaryOfEqualWires_depth]
  exact variableGidney_unit_depth width modulus

/-- The exact arithmetic, complete output and explicit budgets hold for the same actual run. -/
public theorem main (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate (problem width modulus) := by
  refine ⟨algorithm width modulus, ?_⟩
  constructor
  · intro environment _witness Reference input _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input _valid _initialized requirement present
    have same : requirement = StateRequirement.unitary (nativeOperator width modulus) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds environment (nativeOperator width modulus)
      (nativeProgram width modulus)
      (native_matrix (environment := environment.quantum) width modulus)
      (Output.all (context (3 * width)) .unit) input
  · intro environment _witness Reference input _valid _initialized
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed environment rfl rfl
      (nativeProgram width modulus)
      (Output.all (context (3 * width)) .unit) input
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_events width modulus path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_resident width modulus path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact actual_auxiliary width modulus path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact actual_depth width modulus path

end

end QuantumAlg.MAU.Multiplication.VariableGidney
