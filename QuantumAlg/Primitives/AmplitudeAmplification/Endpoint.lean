/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

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
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.State.Requirement
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

/-- No additional state or angle premise restricts the original mathematical source model. -/
public theorem problem_valid {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem M k).valid state := True.intro

/-- Execute actual zero preparation, source amplification, and the explicit complete Output. -/
public def algorithm {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    Algorithm .quantum pre (post n k) .unit where
  run := run M k

/-- The elementary gate count comes from the single actual complete execution. -/
public theorem algorithm_gateCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (algorithm M k).run.code.Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((algorithm M k).run.code.resourcePool path) =
        k * ZeroReflection.elementaryGateCount n :=
  code_gateCount M k path

/-- Ordinary source preparation occurs initially and once in each actual iterate. -/
public theorem algorithm_preparationCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (algorithm M k).run.code.Path) :
    ResourcePool.count (AmplitudeAmplificationSource.preparationEvent n)
      ((algorithm M k).run.code.resourcePool path) = k + 1 :=
  code_preparationCount M k path

/-- Every actual iterate contains precisely one ordinary inverse-source query. -/
public theorem algorithm_inversePreparationCount {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (algorithm M k).run.code.Path) :
    ResourcePool.count (AmplitudeAmplificationSource.inversePreparationEvent n)
      ((algorithm M k).run.code.resourcePool path) = k :=
  code_inversePreparationCount M k path

/-- The actual distinguishing good-reflection query occurs once per iterate. -/
public theorem algorithm_goodReflectionCount {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (path : (algorithm M k).run.code.Path) :
    ResourcePool.count (AmplitudeAmplificationSource.goodReflectionEvent n)
      ((algorithm M k).run.code.resourcePool path) = k :=
  code_goodReflectionCount M k path

private theorem final_observed_state {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) {Reference : Register} (supplied : Execution.Input pre Reference) :
    DensityOperator.observeSelection (post n k).quantumLayout Finset.univ Reference
      ((run M k).finalState Reference supplied.state).quantumMarginal = targetState M k := by
  rw [DensityOperator.observeSelection_all, final_localDensity, DensityOperator.reindex_trans]
  rfl

private theorem actual_state {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    {Reference : Register} (supplied : Execution.Input pre Reference) :
    (stateRequirement M k).Holds supplied ((run M k).finalState Reference supplied.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed (targetState M k) (targetState_normalized M k)).Holds
        (DensityOperator.observeSelection (post n k).quantumLayout Finset.univ Reference
          ((((run M k).finalState Reference supplied.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block,
        final_observed_state M k supplied]
      change (targetState M k).matrix = ((targetState M k).mass : ℝ) • (targetState M k).matrix
      rw [targetState_normalized]
      simp only [one_smul]

/-- The actual complete run solves the original exact amplification problem at every angle and k. -/
public theorem main {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    ∃ candidate : Algorithm .quantum pre (post n k) .unit,
      Algorithm.Solves candidate (problem M k) := by
  refine ⟨algorithm M k, ?_⟩
  constructor
  · intro Reference supplied _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference supplied _valid requirement present
    have same : requirement = stateRequirement M k := List.mem_singleton.mp present
    subst requirement
    exact actual_state M k supplied
  · intro Reference supplied _valid
    exact code_borrowedRestored M k
      (supplied.state.mapClassical fun store => (store, store))
  · intro _Reference _supplied _valid path _supported
    exact le_of_eq (code_events M k path)
  · intro _Reference _supplied _valid path _supported
    exact code_residentSpace M k path
  · intro _Reference _supplied _valid path _supported
    exact code_auxiliarySpace M k path
  · intro _Reference _supplied _valid path _supported
    exact le_of_eq (code_depth M k path)

end

end QuantumAlg.AmplitudeAmplification
