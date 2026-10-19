/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.BernsteinVazirani.Endpoint.Execution
import all QuantumAlg.Algorithms.BernsteinVazirani.Endpoint.Execution

public import QuantumAlg.Algorithms.BernsteinVazirani.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.BernsteinVazirani.Construction
import all QuantumAlg.Algorithms.BernsteinVazirani.Specification
import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Distribution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Restoration
import all QuantumAlg.Primitives.WalshHadamard.Readout.Resources
import all QuantumAlg.Primitives.WalshHadamard.Readout.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Measure.Distribution

/-!
# Complete native Bernstein-Vazirani recovery

The hidden string supplies only the inner-product oracle. The common
Walsh-Hadamard execution prepares its own quantum input and computes the
answer from actual Z writes and finite-bit packing. Its complete Output
retains every live entry. The exact mathematical recovery theorem is
connected to the same execution's final block probabilities, and its paths
satisfy the independent native budgets for every width, including zero.
-/

namespace QuantumAlg.BernsteinVazirani

open WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Independent complete Bernstein-Vazirani recovery contract.

**Input.** Every natural width n and every hidden string s in Fin (2^n), with
quantum access to its mod-two inner-product XOR oracle. There is no additional
promise. The input context is one borrowed unit cell and no quantum systems;
every normalized external-reference extension is admitted. Query and target
systems are prepared by the code itself.
**Output.** The actual n-bit result is the big-endian encoding
`fun index => s.val.testBit (n-1-index.val)`, with probability one. Complete
Output retains the borrowed unit, n+1 prepared quantum systems, n finite
binary measurement cells and the final n-bit string. The target remains
unmeasured. At n=0 the result is the unique empty bit string.
**Resource budget.** Fixed zero preparation of all n+1 qubits, followed by
one target X and 2n+1 Hadamards, charged as 2n+2 native single-qubit gates.
One n-input XOR-oracle call, n binary Z measurements, and one width-tagged
finite-bit packing operation in the built-in bit/word model. Both
resident and auxiliary space are at most n+1 dimension-two systems and 2n
classical bits, with no systems at other dimensions. Unit-event depth is at
most `1+(if n=0 then 3 else 4)+n+1`. At n=0 no measurement is performed and
packing still emits one actual event.
**Success.** Exact recovery with probability one, together with mandatory
joint restoration of the borrowed classical input and external reference.
**Source.** The hidden inner-product problem and exact one-query recovery in
[dW19, qcnotes.tex:1282,1283,1288,1293,1294,1296,1297]. The source explicitly
uses the same query circuit as Deutsch-Jozsa. Native preparation, individual
measurement writes and classical packing are additionally accounted for.
-/
@[expose] public def problem (n : Nat) :
    Problem (model n) pre (post n) (.bits n) where
  Witness := Fin (2 ^ n)
  valid := fun actual hidden _ => actual.quantum = XorOracle.interpretation (oracle hidden)
  initialization := fun _ _ _ => True
  accepts := fun _ hidden => accepts hidden
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => []
  resources :=
    { events := eventBudget n, resident := spaceBudget n, auxiliary := spaceBudget n }
  quantumTimeLimit := depthBudget n

/-- The actual native execution recovers every hidden string with probability one,
preserving borrowed correlations and satisfying the independent complete resource bounds. -/
public theorem main (n : Nat) :
    ∃ candidate : Algorithm (model n) pre (post n) (.bits n),
      Algorithm.Solves candidate (problem n) := by
  refine ⟨algorithm n, ?_⟩
  constructor
  · intro actual hidden Reference input valid _initialized
    have same := environment_eq_of_quantum (oracle hidden) actual valid
    subst actual
    exact le_of_eq (actual_success hidden input).symm
  · intro _actual _hidden _Reference _input _valid _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro actual _hidden Reference input _valid _initialized
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
  · intro _actual _hidden _Reference _input _valid _initialized path _supported
    exact le_of_eq (code_events n path)
  · intro _actual _hidden _Reference _input _valid _initialized path _supported
    exact code_residentSpace n path
  · intro _actual _hidden _Reference _input _valid _initialized path _supported
    exact code_auxiliarySpace n path
  · intro _actual _hidden _Reference _input _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact le_of_eq (code_depth n path)

end

end QuantumAlg.BernsteinVazirani
