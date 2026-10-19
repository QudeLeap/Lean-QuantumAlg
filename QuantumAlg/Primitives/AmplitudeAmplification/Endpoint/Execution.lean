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

/-- Execute actual zero preparation, source amplification, and the explicit complete Output. -/
public def algorithm (n : Nat) (k : Nat) :
    Algorithm (.quantum AlgorithmGate.model
      (AmplitudeAmplificationSource.model n true false))
      pre (post n k) .unit where
  run := run n k

private lemma final_observed_state {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) {Reference : Register}
    (supplied : Execution.OracleInput (model n).classicalOracles pre Reference) :
    DensityOperator.observeSelection (post n k).quantumLayout Finset.univ Reference
      ((run n k).finalState (environment M) Reference supplied.state).quantumMarginal =
        targetState M k := by
  rw [DensityOperator.observeSelection_all, final_localDensity, DensityOperator.reindex_trans]
  rfl

private lemma actual_state {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    {Reference : Register}
    (supplied : Execution.OracleInput (model n).classicalOracles pre Reference) :
    (stateRequirement M k).Holds supplied.caller
      ((run n k).finalState (environment M) Reference supplied.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed (targetState M k) (targetState_normalized M k)).Holds
        (DensityOperator.observeSelection (post n k).quantumLayout Finset.univ Reference
          ((((run n k).finalState (environment M) Reference supplied.state).mapClassical
            (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block,
        final_observed_state M k supplied]
      change (targetState M k).matrix = ((targetState M k).mass : ℝ) • (targetState M k).matrix
      rw [targetState_normalized]
      simp only [one_smul]

end

end QuantumAlg.AmplitudeAmplification
