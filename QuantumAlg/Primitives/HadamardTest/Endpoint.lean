/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.HadamardTest.Endpoint.Execution
import all QuantumAlg.Primitives.HadamardTest.Endpoint.Execution

public import QuantumAlg.Primitives.HadamardTest.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Distribution
import all QuantumAlg.Primitives.HadamardTest.Restoration
import all QuantumAlg.Primitives.HadamardTest.Resources
import all QuantumAlg.Primitives.HadamardTest.Space
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete native Hadamard test with its exact scientific probability

The algorithm prepares one control, executes the actual controlled source
query, measures into a finite classical register, and reads that register.
Its same execution satisfies the independent event, space and depth limits,
complete borrowed-reference restoration, and the original exact probability
[AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Native Hadamard test on the original normalized input.

**Input.** A supplied normalized $n$-qubit vector and controlled access to its
source unitary. The original word is owned because the test may change it.
Every normalized external extension of the promised local state is allowed.
**Output.** The actual binary Z outcome in a finite classical cell, together
with the entire original word and the internally prepared control qubit.
**Resource budget.** One control preparation, two Hadamards, one controlled
source query and one Z measurement; unit-event depth at most five. Resident
and owned auxiliary capacities are $n+1$ qubits and one classical bit. Exactly
one quantum system is newly allocated.
**Success.** The stored zero outcome has probability
$(1+\operatorname{Re}\langle\psi|U|\psi\rangle)/2$. All borrowed observations
and the external reference are restored jointly; measured quantum systems
remain live without an additional state promise.
**Source.** The controlled-unitary construction and real-overlap outcome in
[AJL06, qf2.tex:625-645]. The explicit native ledger follows that same circuit.
-/
@[expose] public def problem (width : Nat) :
    Problem (model width) (pre width) (post width) (.finite 2) where
  Witness := UnitaryOperator (Qubits width) × NormalizedVector (Qubits width)
  valid := fun actual witness state =>
    actual.quantum = UnitarySource.interpretation witness.1 true ∧
      inputPromise witness.2 state.quantumMarginal
  initialization := fun _ _ _ => True
  accepts := fun _ _ _initial result => result = .finite 0
  successLB := fun _ witness => successLB witness.1 witness.2
  states := fun _ _ => []
  resources :=
    { events := eventBudget width
      resident := spaceBudget width
      auxiliary := spaceBudget width }
  quantumTimeLimit := 5

/-- One complete native program solves the source problem for every admissible input. -/
public theorem main (width : Nat) :
    ∃ candidate : Algorithm (model width) (pre width) (post width) (.finite 2),
      Algorithm.Solves candidate (problem width) := by
  refine ⟨algorithm width, ?_⟩
  constructor
  · intro actual witness Reference input promised _initialized
    have same := environment_eq_of_quantum witness.1 actual promised.1
    subst actual
    exact le_of_eq (actual_success witness.1 witness.2 input promised.2)
  · intro _actual _witness _Reference _input _promised _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro actual _witness _Reference input _promised _initialized
    have restored := code_borrowedRestored width actual
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code width).BorrowedRestored _ input.state
      ((code width).execute actual _
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed _)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _actual _witness _Reference _input _promised _initialized path _supported
    exact le_of_eq (code_events width path)
  · intro _actual _witness _Reference _input _promised _initialized path _supported
    exact code_residentSpace width path
  · intro _actual _witness _Reference _input _promised _initialized path _supported
    exact code_auxiliarySpace width path
  · intro _actual _witness _Reference _input _promised _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact code_depth width path

end

end QuantumAlg.HadamardTest
