/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.AmplitudeEstimation.Endpoint.Execution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Endpoint.Execution

public import QuantumAlg.Algorithms.AmplitudeEstimation.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Components.Oracle.AmplitudeAmplification
public import QuantumAlg.Core.Base.Accounting.Weighted
public import Mathlib.Data.Nat.Choose.Basic
public import QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources
import all QuantumAlg.Algorithms.AmplitudeEstimation.Basic
import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Distribution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Restoration
import all QuantumAlg.Algorithms.AmplitudeEstimation.Resources
import all QuantumAlg.Algorithms.AmplitudeEstimation.Space
import all QuantumAlg.Algorithms.AmplitudeEstimation.Specification
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Util.Real.PeriodicSinSq

/-!
# Complete native prepared-state amplitude estimation

The original source model and selected precision determine one actual
prepare, source-query, Z-write, and packing circuit. Complete Output retains
all of its phase/source systems and classical cells. Its own block masses
prove the original additive-error guarantee for every external reference,
while its actual paths satisfy independent native resource and depth bounds.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- General prepared-state amplitude estimation with complete native storage.

**Input.**
- The original intrinsic source preparation $U$, orthogonal good and bad
  states, first-quadrant angle, exact prepared-state decomposition, and
  positive interior-probability lower bound.
- Classical parameters $0<\epsilon\le1$ and $0<\eta\le1$, selecting
  $t=\lceil\log_2(\eta^{-1}/(\epsilon/\pi))\rceil$ phase wires internally.
- Empty runtime storage and any normalized external reference.
**Output.**
- Actual $t$-bit phase data whose sine-squared decoding estimates the source
  good probability.
- Complete Output retaining all $t+n$ prepared systems, $t$ finite binary
  measurement cells, and the packed $t$-bit result.
**Resource budget.**
- Writing $L=2^t-1$, there are $L+1$ ordinary $U$ queries, $L$ ordinary
  $U^\dagger$ queries, and $L$ controlled good-reflection queries.
- Each controlled all-zero reflection is an actual elementary circuit with
  $C(n)$ gates: $C(0)=0$, $C(1)=3$, $C(2)=8$, $C(3)=13$, $C(4)=21$, and
  $C(n)=10n-21$ for $n\ge5$. The complete unitary uses
  $2t+LC(n)+5\binom{t}{2}+3\lfloor t/2\rfloor$ elementary gates.
- The original valid domain implies $t\ge2$. Large reflections borrow a
  different existing phase wire and restore its arbitrary value exactly,
  including the controlled global phase. Thus no extra qubit is allocated
  on the admitted domain. The total definition at $t=1,n\ge3$ honestly
  prepares and retains one extra work system.
- One zero preparation per actual qubit, $t$ binary Z measurements, and one packing
  operation are charged. Resident and auxiliary capacities are $t+n$
  dimension-two systems and $2t$ classical bits.
- Unit-event depth is
  $1+(1+([t>0]+(L(3+C(n))+t+5\binom{t}{2}+3\lfloor t/2\rfloor)))+t+1$.
**Success.**
- The actual additive-error event has probability at least $1-\eta$.
- The complete external reference is restored independently of this event.
**Source.**
- Preparation, signed eigenphases, selected precision, and the additive-error
  guarantee in [Lin22, appqpe.tex:187-254].
- Native execution additionally records its actual preparation, measurements,
  retained cells, and packing.
-/
@[expose] public def problem (n : Nat) (eps η : Real) (nonnegative : 0 ≤ η) :
    Problem (model n) pre (post (selectedPhaseQubits eps η) n)
      (.bits (selectedPhaseQubits eps η)) where
  Witness := GeneralAmplitudeEstimationInput n
  valid := fun environment E _ =>
    environment.quantum = AmplitudeAmplificationSource.interpretation
      E.source.preparation E.source.good true true ∧
      0 < eps ∧ eps ≤ 1 ∧ 0 < η ∧ η ≤ 1
  initialization := fun _ _ _ => True
  accepts := fun _ E => accepts E eps
  successLB := fun _ _ => successLB η nonnegative
  states := fun _ _ => []
  resources :=
    { events := eventBudget n (selectedPhaseQubits eps η)
      resident := spaceBudget (selectedPhaseQubits eps η) n
      auxiliary := spaceBudget (selectedPhaseQubits eps η) n }
  quantumTimeLimit := depthBudget (selectedPhaseQubits eps η) n

/-- The named public execution satisfies its full independent input,
state and resource contract for every admitted source interpretation. -/
private lemma complete_correct (n : Nat) (eps η : Real) (nonnegative : 0 ≤ η) :
    Algorithm.Solves (algorithm n eps η) (problem n eps η nonnegative) := by
  constructor
  · intro environment E Reference input promised _initialized
    have same := sourceEnvironment_eq E environment promised.1
    subst environment
    exact actual_success E eps η
      (selectedPhaseQubits_pos promised.2.1 promised.2.2.1 promised.2.2.2.1 promised.2.2.2.2)
      promised.2.1 promised.2.2.1 promised.2.2.2.1 promised.2.2.2.2 input
  · intro _environment _E _Reference _input _promised _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro environment _E Reference input _promised _initialized
    have restored := code_borrowedRestored n (selectedPhaseQubits eps η) environment
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code n (selectedPhaseQubits eps η)).BorrowedRestored Reference input.state
      ((code n (selectedPhaseQubits eps η)).execute environment Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _environment _E _Reference _input _promised _initialized path _supported
    exact le_of_eq (code_events n (selectedPhaseQubits eps η) path)
  · intro _environment _E _Reference _input _promised _initialized path _supported
    exact code_residentSpace n (selectedPhaseQubits eps η) path
  · intro _environment _E _Reference _input _promised _initialized path _supported
    exact code_auxiliarySpace n (selectedPhaseQubits eps η) path
  · intro _environment _E _Reference _input _promised _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact code_depth n (selectedPhaseQubits eps η) path

/-- The original prepared-state amplitude-estimation problem is solved by one fixed execution
for all source witnesses, with complete storage, joint reference preservation and native budgets. -/
public theorem main (n : Nat) (eps η : Real) (nonnegative : 0 ≤ η) :
    ∃ candidate : Algorithm (model n) pre (post (selectedPhaseQubits eps η) n)
        (.bits (selectedPhaseQubits eps η)),
      Algorithm.Solves candidate (problem n eps η nonnegative) :=
  ⟨algorithm n eps η, complete_correct n eps η nonnegative⟩

end

end QuantumAlg.AmplitudeEstimation
