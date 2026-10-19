/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.AmplitudeAmplification.Endpoint.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Endpoint.Execution

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Primitives.AmplitudeAmplification.Specification
public import QuantumAlg.Primitives.AmplitudeAmplification.Construction
public import QuantumAlg.Components.Oracle.ZeroReflection.Resources
public import QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Execution.Laws
import all QuantumAlg.Primitives.AmplitudeAmplification.Resources
import all QuantumAlg.Primitives.AmplitudeAmplification.Counts
import all QuantumAlg.Primitives.AmplitudeAmplification.Space
import all QuantumAlg.Primitives.AmplitudeAmplification.Restoration
import all QuantumAlg.Primitives.AmplitudeAmplification.Specification
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Complete native amplitude amplification at every source angle and iteration count

The endpoint executes actual preparation and source queries with an elementary
positive zero reflection. Its own final density proves the original exact
amplified state, with every prepared system retained and every external
reference restored. Resource formulas are checked against that same run.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Complete native source-query amplitude amplification.

**Input.** The original normalized good/bad source plane, measurement-free
preparation unitary A and its exact prepared-state decomposition, with any
real angle and any natural iteration count k. Runtime input is empty and all
normalized external-reference states are admitted.
**Output.** The source has bad/good amplitudes cos((2k+1)θ) and sin((2k+1)θ).
Every selected helper is retained in its original prepared zero state; the
complete Output keeps the entire joint source/helper register and returns unit.
**Resource budget.** One zero preparation per actual source/helper qubit, k+1 ordinary A
queries, k inverse-A queries and k distinguishing good-reflection queries.
Each known positive zero reflection uses the independently counted elementary
gates, for k times that count in total. There are n+h owned quantum systems,
where h is zero for k=0 or n≤3 and otherwise one; no classical bits exist.
Unit-event depth is at most 2+k(3+D(n)), where D is the elementary reflection count.
**Success.** Probability one with the exact joint output-state requirement and
mandatory restoration of the complete external reference, at every angle and k.
**Source.** Measurement-free amplification and the exact good/bad-plane rotation
[dW19, qcnotes.tex:2914-2964]. The known reflection is synthesized with exact
phase and a restored helper; no controlled access to A is assumed.
-/
@[expose] public def problem (n k : Nat) :
    Problem (.quantum AlgorithmGate.model
      (AmplitudeAmplificationSource.model n true false))
      pre (post n k) .unit where
  Witness := IntrinsicAmplitudeAmplificationModel n
  valid := fun actual source _ =>
    actual.quantum = Native.interpretation source.preparation source.good
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ source => [stateRequirement source k]
  resources :=
    { events := eventBudget n k
      resident := spaceBudget n k
      auxiliary := spaceBudget n k }
  quantumTimeLimit := depthBudget n k

/-- The single width-and-iteration program satisfies all seven obligations for every source. -/
private lemma complete_correct (n k : Nat) :
    Algorithm.Solves (algorithm n k) (problem n k) := by
  constructor
  · intro _actual _source Reference supplied _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro actual M Reference supplied valid _initialized requirement present
    have sameEnvironment := environment_eq_of_quantum M actual valid
    subst actual
    have same : requirement = stateRequirement M k := List.mem_singleton.mp present
    subst requirement
    exact actual_state M k supplied
  · intro actual _source Reference supplied _valid _initialized
    have restored := code_borrowedRestored n k actual
      (supplied.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical supplied.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code n k).BorrowedRestored _ supplied.state
      ((code n k).execute actual _
        (supplied.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed _)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _actual _source _Reference _supplied _valid _initialized path _supported
    exact le_of_eq (code_events n k path)
  · intro _actual _source _Reference _supplied _valid _initialized path _supported
    exact code_residentSpace n k path
  · intro _actual _source _Reference _supplied _valid _initialized path _supported
    exact code_auxiliarySpace n k path
  · intro _actual _source _Reference _supplied _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact code_depth n k path

/-- One fixed complete run solves the exact amplification problem at every source angle. -/
public theorem main (n k : Nat) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model
      (AmplitudeAmplificationSource.model n true false)) pre (post n k) .unit,
      Algorithm.Solves candidate (problem n k) :=
  ⟨algorithm n k, complete_correct n k⟩

end

end QuantumAlg.AmplitudeAmplification
