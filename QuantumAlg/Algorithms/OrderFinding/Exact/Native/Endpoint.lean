/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Specification
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Success
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Restoration
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Resources
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Complete native exact-dyadic order finding

One connected source sampler and stored-bit decoder meet the independent
exact-grid specification, with actual Born success, borrowed restoration, and
pathwise event, depth and space bounds.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The public result is produced by the connected native source and decoder. -/
public def algorithm (t width : Nat) :
    Algorithm (Sampling.Native.model t width)
      Sampling.Native.pre (post t width) (.unsignedWord t) where
  run := run t width

private lemma actual_success {N x t width r : Nat}
    (access : ModExpOracleAccess N x t width)
    (hinput : OrderFinding.Input N x r) (dyadic : r ∣ 2 ^ t)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.model t width).classicalOracles Sampling.Native.pre Reference) :
    ((run t width).relationalDistribution (Sampling.Native.environment access) input).toOuterMeasure
      {pair | SuccessfulOutcome r pair.2} = 1 := by
  have projection :
      ((run t width).relationalDistribution (Sampling.Native.environment access)
        input).toOuterMeasure
          {pair | SuccessfulOutcome r pair.2} =
        ((run t width).outputDistribution (Sampling.Native.environment access) input).toOuterMeasure
          {output | SuccessfulOutcome r output} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection]
  exact successProbability_eq_one access hinput dyadic input

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
public lemma algorithm_solves (N x t width : Nat) :
    Algorithm.Solves (algorithm t width) (problem N x t width) := by
  constructor
  · intro environment witness Reference input valid _initialized
    rcases valid with ⟨same, _positiveWidth, hinput, dyadic⟩
    have canonical := Sampling.Native.environment_eq_of_quantum witness.access environment same
    subst environment
    simp only [Algorithm.relationalDistribution, algorithm]
    exact le_of_eq (actual_success witness.access hinput dyadic input).symm
  · intro _environment _witness _Reference _input _valid _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro environment _witness Reference input _valid _initialized
    have restored := code_borrowedRestored t width environment
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code t width).BorrowedRestored Reference input.state
      ((code t width).execute environment Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact code_events_le t width path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact code_resident_le t width path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    exact code_auxiliary_le t width path
  · intro _environment _witness _Reference _input _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact code_depth_le t width path

/-- One fixed source and decoder solve every admitted exact dyadic source interpretation. -/
public theorem main (N x t width : Nat) :
    ∃ candidate : Algorithm (Sampling.Native.model t width)
        Sampling.Native.pre (post t width) (.unsignedWord t),
      Algorithm.Solves candidate (problem N x t width) :=
  ⟨algorithm t width, algorithm_solves N x t width⟩

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
