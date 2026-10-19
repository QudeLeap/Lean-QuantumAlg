/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Grover.Endpoint.Execution
import all QuantumAlg.Algorithms.Grover.Endpoint.Execution

public import QuantumAlg.Algorithms.Grover.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Algorithms.Grover.Distribution
import all QuantumAlg.Algorithms.Grover.Restoration
import all QuantumAlg.Algorithms.Grover.Resources
import all QuantumAlg.Algorithms.Grover.Space
import all QuantumAlg.Algorithms.Grover.Specification
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution

/-!
# Grover's complete native endpoint

The named algorithm contains the one actual prepare, Grover-unitary, Z-write
and packing execution. Its explicit complete output keeps every quantum
system and classical cell. The exact probability and native gate/query
counts are proved on this execution in addition to the independent Solves
contract [dW19, qcnotes.tex:2760-2852].
-/

namespace QuantumAlg.GroverSearch

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Independent complete Grover search contract.

**Input.** A positive width n, a predicate on all 2^n indices with exactly
t > 0 marked indices, and any iteration count k. The borrowed runtime input
is a unit cell with no quantum systems; arbitrary normalized external-reference
extensions are admitted. The search register is prepared internally.
**Output.** The actual n-bit search index is accepted precisely when the
predicate marks its canonical big-endian decoding. Every prepared search and
work system, n finite measurement cells, the packed result and borrowed unit
remain in complete Output after measurement. Only the search wires are measured.
**Resource budget.** One zero preparation per actual qubit,
k phase queries, n+2nk Hadamards outside the reflections, the independently
specified elementary S0 events, n binary Z measurements and one packing operation.
For n=1,2,3 a reflection uses respectively 1,5,10 elementary gates and no work.
For n>=4 it uses 2n+3 single-qubit gates and L(n-1) Toffoli gates,
where L(3)=4, L(4)=10 and L(m)=8(m-3) for m>=5. The total elementary gate count is
n+k(2n+S0Count(n)). A single additional work system is needed only when k>0 and
n>=4; resident and auxiliary capacities both count it and the 2n retained
classical bits. Parallel H layers have unit duration when nonempty; each S0
sequence has duration S0Count(n). The exact complete unit-event depth is
1+delta(n)+k(1+2delta(n)+S0Count(n))+n+1, with delta(n)=1 for positive width.
**Success.** The actual marked-result probability is exactly
sin((2k+1) arcsin(sqrt(t/2^n))) squared. The borrowed input and its full external
reference are restored jointly, independently of the output state promise.
**Source.** The starting state, two reflections and exact marked-event
probability in [dW19, qcnotes.tex:2760-2852]. The native execution additionally
charges its actual basis preparation, Z writes, retained cells and packing.
-/
@[expose] public def problem (n k : Nat) :
    Problem (model n) pre (post n k) (.bits n) where
  Witness := Fin (2 ^ n) → Bool
  valid := fun actual marked _ =>
    actual.quantum = UnitarySource.interpretation (phaseOracleOp marked) false ∧
      0 < n ∧ 0 < markedCount marked
  initialization := fun _ _ _ => True
  accepts := fun _ marked => accepts marked
  successLB := fun _ marked => successLB n (markedCount marked) k
  states := fun _ _ => []
  resources :=
    { events := eventBudget n k, resident := spaceBudget n k, auxiliary := spaceBudget n k }
  quantumTimeLimit := depthBudget n k

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
private lemma complete_correct (n k : Nat) :
    Algorithm.Solves (algorithm n k) (problem n k) := by
  constructor
  · intro actual marked Reference input promised _initialized
    have same := environment_eq_of_quantum marked actual promised.1
    subst actual
    exact le_of_eq (actual_success marked k rfl promised.2.2 input).symm
  · intro _actual _marked _Reference _input _promised _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro actual _marked Reference input _promised _initialized
    have restored := code_borrowedRestored n k actual
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code n k).BorrowedRestored _ input.state
      ((code n k).execute actual _
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed _)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _actual _marked _Reference _input _promised _initialized path _supported
    exact le_of_eq (code_events n k path)
  · intro _actual _marked _Reference _input _promised _initialized path _supported
    exact code_residentSpace n k path
  · intro _actual _marked _Reference _input _promised _initialized path _supported
    exact code_auxiliarySpace n k path
  · intro _actual _marked _Reference _input _promised _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact code_depth n k path

/-- The actual search execution solves the original positive-width problem with independent
complete event, space and depth bounds and mandatory joint borrowed restoration. -/
public theorem main (n k : Nat) :
    ∃ candidate : Algorithm (model n) pre (post n k) (.bits n),
      Algorithm.Solves candidate (problem n k) :=
  ⟨algorithm n k, complete_correct n k⟩

end

end QuantumAlg.GroverSearch
