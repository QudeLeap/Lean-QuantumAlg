/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Endpoint.Execution
import all QuantumAlg.Algorithms.QPE.Endpoint.Execution

public import QuantumAlg.Algorithms.QPE.Specification
public import QuantumAlg.Algorithms.QPE.Construction
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Measure.Distribution
public import Mathlib.Analysis.Normed.Group.AddCircle
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.WindowProbability
import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Distribution
import all QuantumAlg.Algorithms.QPE.Restoration
import all QuantumAlg.Algorithms.QPE.Resources
import all QuantumAlg.Algorithms.QPE.Space
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Complete native quantum phase estimation

The supplied borrowed eigenstate, internally prepared phase word, actual
controlled-power ladder, individual Z writes and stored bit packing belong
to one execution. Its own probabilities establish the original phase-window
bound, while complete Output and unconditional joint borrowed restoration
retain every live physical system and its reference correlations.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Quantum phase estimation on the supplied borrowed eigenstate.

**Input.**
- An $n$-qubit unitary $U$, its borrowed normalized eigenstate $\ket{\psi}$
  satisfying $U\ket{\psi}=e^{2\pi i\theta}\ket{\psi}$, and controlled-$U$ access.
- A positive precision width $t$ and every normalized extension of the
  promised local pure input by an external reference.
- The phase prefix is prepared internally in $\ket{0^t}$.
**Output.**
- Actual stored $t$-bit phase data with circular precision $2^{-t}$.
- Complete Output retaining the $n$ borrowed source systems, $t$ owned phase
  systems, $t$ binary measurement cells, and the packed $t$-bit result.
**Resource budget.**
- Exactly $2^t-1$ controlled-$U$ queries, $2t+3\binom{t}{2}$ native
  single-qubit gates, and $2\binom{t}{2}+3\lfloor t/2\rfloor$ CNOT gates.
- The inverse Fourier readout includes every native controlled-phase and SWAP expansion.
- Exactly $t$ zero preparations, $t$ individual Z measurements, and one bit-packing operation.
- Resident capacity is $t+n$ dimension-two systems and $2t$ classical bits;
  auxiliary capacity is $t$ dimension-two systems and $2t$ classical bits.
- At positive width, unit-event depth is bounded by
  $2^t+2+2t+5\binom{t}{2}+3\lfloor t/2\rfloor$.
**Success.**
- The original circular phase-window event has probability at least $4/\pi^2$.
- The complete borrowed eigenstate and external reference are restored jointly,
  independently of the success event; the owned phase systems remain live.
**Source.**
- QPE, the controlled-power ladder, and its success analysis in
  [Lin22, phaseestimation.tex:510-521,647-715].
- Exact preparation and inverse-QFT native gate counts come from the same
  structural source circuit; execution records its actual Z writes and packing.
-/
@[expose] public def problem (n t : Nat) :
    Problem (model n) (pre t n) (post t n) (.bits t) where
  Witness := QPEEigenstateInput n
  valid := fun environment P state =>
    environment.quantum = UnitarySource.interpretation P.unitary true ∧
      0 < t ∧ inputPromise P t state.quantumMarginal
  initialization := fun _ _ _ => True
  accepts := fun _ P => accepts P t
  successLB := fun _ _ => successLB
  states := fun _ _ => []
  resources :=
    { events := eventBudget n t
      resident := residentBudget t n
      auxiliary := auxiliaryBudget t }
  quantumTimeLimit := depthBudget t

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
private lemma complete_correct (n t : Nat) :
    Algorithm.Solves (algorithm n t) (problem n t) := by
  constructor
  · intro environment P Reference input promised _initialized
    have same := sourceEnvironment_eq P.unitary environment promised.1
    subst environment
    exact actual_success P t input promised.2.2
  · intro _environment _P _Reference _input _promised _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro environment P Reference input promised _initialized
    have same := sourceEnvironment_eq P.unitary environment promised.1
    subst environment
    have promisedState : inputPromise P t
        (input.state.mapClassical
          (fun value => (value.1, (value.2, value.1)))).quantumMarginal.marginalLeft := by
      have localPromise := promised.2.2
      rw [Execution.Input.localState_quantumMarginal,
        Execution.OracleInput.oracleInput_caller_quantumMarginal] at localPromise
      simpa only [ExecutionState.mapClassical_quantumMarginal] using localPromise
    have restored := code_borrowedRestored P t
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))) promisedState
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code n t).BorrowedRestored Reference input.state
      ((code n t).execute (sourceEnvironment P.unitary) Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _environment _P _Reference _input _promised _initialized path _supported
    exact le_of_eq (code_events n t path)
  · intro _environment _P _Reference _input _promised _initialized path _supported
    exact code_residentSpace n t path
  · intro _environment _P _Reference _input _promised _initialized path _supported
    exact code_auxiliarySpace n t path
  · intro _environment _P _Reference _input _promised _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact code_depth n t path

/-- The original borrowed-eigenstate phase-estimation problem is solved by the same actual
execution with complete output, joint borrowed restoration and independent native budgets. -/
public theorem main (n t : Nat) :
    ∃ candidate : Algorithm (model n) (pre t n) (post t n) (.bits t),
      Algorithm.Solves candidate (problem n t) :=
  ⟨algorithm n t, complete_correct n t⟩

end

end QuantumAlg.QuantumPhaseEstimation
