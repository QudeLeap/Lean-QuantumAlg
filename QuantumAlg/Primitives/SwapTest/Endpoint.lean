/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.SwapTest.Endpoint.Execution
import all QuantumAlg.Primitives.SwapTest.Endpoint.Execution

public import QuantumAlg.Primitives.SwapTest.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Primitives.SwapTest.Specification
import all QuantumAlg.Primitives.SwapTest.Execution
import all QuantumAlg.Primitives.SwapTest.Probability
import all QuantumAlg.Primitives.SwapTest.Resources
import all QuantumAlg.Primitives.SwapTest.Restoration
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete elementary SWAP test with its exact scientific probability

The same complete measured execution supplies the source probability,
independent native resource limits and external reference restoration
[BCWdW01, main.tex:287-329].
-/

namespace QuantumAlg.SwapTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Elementary measured SWAP test on the original pair of normalized inputs.

**Input.** Two normalized $n$-qubit vectors in the two owned supplied registers.
Every reference extension with this promised local product state is allowed.
**Output.** The actual binary Z result, both complete original words, and the
internally prepared control. The measured quantum systems remain live.
**Resource budget.** One control preparation, two Hadamards, $2n$ CNOTs, $n$ Toffolis
and one Z measurement. Unit-duration depth is at most $3n+4$. Resident
and owned auxiliary space are each at most $2n+1$ qubits and one classical bit.
Exactly one qubit is newly allocated; no additional work register is needed.
**Success.** The stored one outcome has exact probability
$(1-|\langle\psi|\phi\rangle|^2)/2$. All borrowed/reference correlations
are restored. The owned input words may change.
**Source.** The measured controlled-swap construction and its exact probability
[BCWdW01, main.tex:287-329]. The elementary native counts follow the explicit
CNOT/Toffoli/CNOT implementation of each controlled bit exchange.
-/
@[expose] public def problem (width : Nat) :
    Problem model (pre width) (post width) (.finite 2) where
  Witness := NormalizedVector (Qubits width) × NormalizedVector (Qubits width)
  valid := fun _ witness state => inputPromise witness.1 witness.2 state.quantumMarginal
  initialization := fun _ _ _ => True
  accepts := fun _ _ _initial result => result = .finite 1
  successLB := fun _ witness => successLB witness.1 witness.2
  states := fun _ _ => []
  resources :=
    { events := eventBudget width
      resident := spaceBudget width
      auxiliary := spaceBudget width }
  quantumTimeLimit := 3 * width + 4

/-- One complete native program solves the source problem for every admissible input. -/
public theorem main (width : Nat) :
    ∃ candidate : Algorithm model (pre width) (post width) (.finite 2),
      Algorithm.Solves candidate (problem width) := by
  refine ⟨algorithm width, ?_⟩
  constructor
  · intro actual witness Reference input promised _initialized
    exact le_of_eq (actual_success actual witness.1 witness.2 input promised)
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

end QuantumAlg.SwapTest
