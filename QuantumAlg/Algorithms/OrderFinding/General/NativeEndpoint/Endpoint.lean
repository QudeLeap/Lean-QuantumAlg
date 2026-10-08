/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Success
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Restoration
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Resources
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Complete native general order finding

The actual source circuit writes the phase bits, and finite recovery reads
those same cells and the borrowed canonical base. Its Born success bound,
joint borrowed restoration, and independent event, depth and space budgets
are properties of this one execution.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The public result is produced by the connected native source and recovery run. -/
public def algorithm {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) :
    Algorithm (Sampling.Native.Framed.model access)
      (pre width) (post t width) (outputShape t) where
  run := run hinput access

private theorem actual_success {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model access).classicalOracles (pre width) Reference)
    (valid : HasCanonicalBase hinput access input.caller.localState)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2) :
    (successLB r).value ≤
      ((run hinput access).relationalDistribution input).toOuterMeasure
        {pair | (problem hinput access).accepts pair.1 pair.2} := by
  have projection :
      ((run hinput access).relationalDistribution input).toOuterMeasure
          {pair | (problem hinput access).accepts pair.1 pair.2} =
        ((run hinput access).outputDistribution input).toOuterMeasure
          {output | SuccessfulOutcome r output} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection]
  exact output_successProbability_ge hinput access input valid hregister hupper

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
public theorem algorithm_solves {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) :
    Algorithm.Solves (algorithm hinput access) (problem hinput access) := by
  constructor
  · intro Reference input valid _initialized
    rcases valid with ⟨canonical, _positiveWidth, hregister, hupper⟩
    simp only [Algorithm.relationalDistribution, algorithm]
    exact actual_success hinput access input canonical hregister hupper
  · intro _Reference _input _valid _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _valid _initialized
    have restored := code_borrowedRestored hinput access
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code hinput access).BorrowedRestored Reference input.state
      ((code hinput access).execute Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  · intro _Reference _input _valid _initialized path _supported
    exact code_events_le hinput access path
  · intro _Reference _input _valid _initialized path _supported
    exact code_resident_le hinput access path
  · intro _Reference _input _valid _initialized path _supported
    exact code_auxiliary_le hinput access path
  · intro _Reference _input _valid _initialized path _supported
    exact code_depth_le hinput access path


/-- One complete native algorithm solves the original general order-finding
window with source success, full borrowed restoration and actual budgets. -/
public theorem main {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) :
    ∃ candidate : Algorithm (Sampling.Native.Framed.model access)
        (pre width) (post t width) (outputShape t),
      Algorithm.Solves candidate (problem hinput access) :=
  ⟨algorithm hinput access, algorithm_solves hinput access⟩

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
