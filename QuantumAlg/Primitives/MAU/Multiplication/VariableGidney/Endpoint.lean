/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
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

private def wordBasisEquiv (width : Nat) :
    (context (3 * width)).register.Index ≃ (Qubits (encoding width).width).Index :=
  (basisEquiv (3 * width)).trans
    (finCongr (congrArg (fun count : Nat => 2 ^ count) (by
      change 3 * width = width + (width + width)
      omega)))

private def nativeOperator (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryOperator (context (3 * width)).register :=
  UnitaryOperator.reindex (wordBasisEquiv width).symm (wordVariableOperator width modulus)

private def nativeProgram (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit (context (3 * width)).register :=
  UnitaryCircuit.reindex (wordBasisEquiv width).symm (program width modulus)

private theorem native_matrix (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (nativeProgram width modulus).matrix = nativeOperator width modulus :=
  (UnitaryCircuit.reindex_matrix (R := Qubits (encoding width).width)
    (S := (context (3 * width)).register) (wordBasisEquiv width).symm
    (program width modulus)).trans
      (congrArg (fun operator : UnitaryOperator (Qubits (encoding width).width) =>
        UnitaryOperator.reindex (wordBasisEquiv width).symm operator)
        (variableGidney_matrix width modulus))

private theorem placement (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (nativeProgram width modulus).physical_idx = (context (3 * width)).physicalIdx := by
  change (program width modulus).physical_idx = (context (3 * width)).physicalIdx
  rw [variableGidney_physical, ownedQubits_physicalIdx]

private def code (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    Circuit (context (3 * width)) (context (3 * width)) :=
  .unitary (nativeProgram width modulus) (placement width modulus)

/-- Independent complete variable-product execution contract.

**Input.** Three supplied owned width-qubit words in any normalized joint
state, including mixed states and correlations with an arbitrary reference.
The fitted modulus is a compilation parameter. Neither quantum input is
required to be nonzero or invertible; the modulus need not be odd.

**Output.** All three words remain live. On canonical target labels z<N,
the exact arithmetic action is (x,y,z) to (x,y,(z+x*y) mod N). Noncanonical
target labels are fixed. The full independent permutation acts jointly
with the reference identity, preserving every relative phase.

**Resource budget.** The native budget is width controlled MAC budgets,
with an additional dimension-two control on each original MAC coordinate.
The explicit total-event and unit-depth bound is
width*(width*stageEventBound(width)). Resident and owned auxiliary pools
both contain the three supplied words, exactly 3*width dimension-two
systems. The run allocates no other quantum or classical storage.

**Success.** The unit result has probability one; the full-state target
holds for every input. Width zero is the empty, zero-event instance.

**Source.** Binary controlled additions [VBE95, 9511018.tex:333-367],
instantiated with exact pivot-flip offsets [G17, paper.tex:319-334].
-/
public def problem (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    Problem .quantum (context (3 * width)) (context (3 * width)) .unit where
  valid := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (nativeOperator width modulus)]
  resources :=
    { events := nativeBudget width
      resident := space (3 * width)
      auxiliary := space (3 * width) }
  depth := .quantum (fun _ => 1) (eventBound width)

/-- Execute the actual three-word circuit and retain its complete output. -/
public def algorithm (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    Algorithm .quantum (context (3 * width)) (context (3 * width)) .unit where
  run := { code := code width modulus, output := Output.all (context (3 * width)) .unit }

/-- The exact arithmetic, complete output and explicit budgets hold for the same actual run. -/
public theorem main (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    ∃ candidate, Algorithm.Solves candidate (problem width modulus) := by
  refine ⟨algorithm width modulus, ?_⟩
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = StateRequirement.unitary (nativeOperator width modulus) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (nativeOperator width modulus)
      (nativeProgram width modulus) (placement width modulus) (native_matrix width modulus)
      (Output.all (context (3 * width)) .unit) input
  · intro Reference input _valid
    exact Circuit.borrowedRestored_unitary_noBorrowed rfl rfl
      (nativeProgram width modulus) (placement width modulus)
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    change ResourcePool.ofList (nativeProgram width modulus).eventTrace ≤ nativeBudget width
    exact (UnitaryCircuit.ofList_eventTrace_eq_eventCost (nativeProgram width modulus)).le.trans
      (variableGidney_native_budget width modulus)
  · intro _Reference _input _valid path _supported axis
    change Nat.max ((context (3 * width)).residentSpace axis) 0 ≤ space (3 * width) axis
    rw [ownedQubits_resident]
    exact le_of_eq (Nat.max_zero _)
  · intro _Reference _input _valid path _supported axis
    change Nat.max ((context (3 * width)).auxiliarySpace axis) 0 ≤ space (3 * width) axis
    rw [ownedQubits_auxiliary]
    exact le_of_eq (Nat.max_zero _)
  · intro _Reference _input _valid path _supported
    exact variableGidney_unit_depth width modulus

end

end QuantumAlg.MAU.Multiplication.VariableGidney
