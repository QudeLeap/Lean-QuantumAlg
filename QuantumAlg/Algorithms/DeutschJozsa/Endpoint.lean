/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.DeutschJozsa.Endpoint.Execution
import all QuantumAlg.Algorithms.DeutschJozsa.Endpoint.Execution

public import QuantumAlg.Algorithms.DeutschJozsa.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Algorithms.DeutschJozsa.Construction
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Algorithms.DeutschJozsa.Specification
import all QuantumAlg.Algorithms.DeutschJozsa.DistributionLaws
import all QuantumAlg.Primitives.WalshHadamard.Readout.Restoration
import all QuantumAlg.Primitives.WalshHadamard.Readout.Resources
import all QuantumAlg.Primitives.WalshHadamard.Readout.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# The complete native Deutsch-Jozsa endpoint

The sole executable circuit prepares the query and target, executes the
original oracle circuit, writes each query measurement to its own finite
classical cell, and packs the actual results. Complete Output retains every
live entry. The proof uses probabilities and paths from that same execution,
including preservation of its borrowed classical input and arbitrary
external-reference correlations.
-/

namespace QuantumAlg.DeutschJozsa

open WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Independent complete Deutsch-Jozsa decision contract.

**Input.** For every natural width n, an oracle on all 2^n binary inputs,
promised constant or balanced. The runtime input is the original borrowed
unit cell, with no supplied quantum systems. Every normalized external
reference extension of this local input is admitted.
**Output.** The actual n-bit measured query result is zero exactly when the
oracle is constant. All n+1 prepared quantum systems, n finite binary result
cells, the final n-bit string, and the borrowed unit remain in complete Output.
The target quantum system is not measured or released. At n = 0 the result is
the unique empty bit string and there are zero measurement instructions.
**Resource budget.** Fixed zero preparation of all n+1 qubits, followed by
one target X and 2n+1 Hadamards, charged as 2n+2 native single-qubit gates.
One declared n-input XOR-oracle call, n binary Z measurements,
and one width-tagged finite-bit packing operation. Resident and auxiliary
space are at most n+1 dimension-two systems and 2n classical bits, with zero
systems of other dimensions. Unit-event depth is at most
1+(if n=0 then 3 else 4)+n+1; packing still executes at n=0.
**Success.** Probability one under the original promise, with mandatory joint
restoration of the borrowed input and arbitrary external reference.
**Source.** The promise, phase-query construction, signed amplitude and exact
decision in [dW19, qcnotes.tex:1179,1193,1245,1251,1253,1255]; the single XOR
query with its target factor in [CEMM98, cemm6.tex:326,342,379,403]. The native
execution additionally accounts for its actual preparation, measurement
storage and final classical packing instructions.
-/
@[expose] public def problem (n : Nat) :
    Problem (model n) pre (post n) (.bits n) where
  Witness := WalshHadamard.Oracle n
  valid := fun actual f _ => actual.quantum = XorOracle.interpretation f ∧ Promise f
  initialization := fun _ _ _ => True
  accepts := fun _ f => accepts f
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => []
  resources := { events := eventBudget n, resident := spaceBudget n, auxiliary := spaceBudget n }
  quantumTimeLimit := depthBudget n

/-- For every width, including zero, the native execution solves the original promise problem
with probability one and the independently stated complete resource bounds. -/
public theorem main (n : Nat) :
    ∃ candidate : Algorithm (model n) pre (post n) (.bits n),
      Algorithm.Solves candidate (problem n) := by
  refine ⟨algorithm n, ?_⟩
  constructor
  · intro actual f Reference input valid _initialized
    have same := environment_eq_of_quantum f actual valid.1
    subst actual
    exact le_of_eq (actual_success f valid.2 input).symm
  · intro _actual _f _Reference _input _promised _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro actual _f Reference input _valid _initialized
    have restored := code_borrowedRestored n actual
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code n).BorrowedRestored Reference input.state
      ((code n).execute actual Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _actual _f _Reference _input _promised _initialized path _supported
    exact le_of_eq (code_events n path)
  · intro _actual _f _Reference _input _promised _initialized path _supported
    exact code_residentSpace n path
  · intro _actual _f _Reference _input _promised _initialized path _supported
    exact code_auxiliarySpace n path
  · intro _actual _f _Reference _input _promised _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact le_of_eq (code_depth n path)

end

end QuantumAlg.DeutschJozsa
