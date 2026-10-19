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
public def algorithm {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat) :
    Algorithm (Sampling.Native.Framed.model t width)
      (pre width) (post t width) (outputShape t) where
  run := run spec t

private lemma actual_success {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model t width).classicalOracles (pre width) Reference)
    (valid : HasCanonicalBase hinput access input.caller.localState)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2) :
    (successLB r).value ≤
      ((run (modulusSpec hinput access) t).relationalDistribution (Sampling.Native.environment
        access) input).toOuterMeasure
        {pair | SuccessfulOutcome r pair.2} := by
  have projection :
      ((run (modulusSpec hinput access) t).relationalDistribution (Sampling.Native.environment
        access) input).toOuterMeasure
          {pair | SuccessfulOutcome r pair.2} =
        ((run (modulusSpec hinput access) t).outputDistribution (Sampling.Native.environment
          access) input).toOuterMeasure
          {output | SuccessfulOutcome r output} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection]
  exact output_successProbability_ge hinput access input valid hregister hupper

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
public lemma algorithm_solves {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (x t : Nat) :
    Algorithm.Solves (algorithm spec t) (problem spec x t) := by
  constructor
  · intro environment order Reference input valid _initialized
    rcases valid with ⟨hinput, same, canonical, _positiveWidth, hregister, hupper⟩
    have equal := Sampling.Native.environment_eq_of_quantum (sourceAccess spec x t)
      environment same
    subst environment
    change (successLB order).value ≤
      ((run spec t).relationalDistribution
        (Sampling.Native.environment (sourceAccess spec x t)) input).toOuterMeasure
          {pair | SuccessfulOutcome order pair.2}
    have recoveredSpec : modulusSpec hinput (sourceAccess spec x t) = spec := by
      cases spec
      rfl
    have success := actual_success hinput (sourceAccess spec x t)
      input canonical hregister hupper
    rw [recoveredSpec] at success
    exact success
  · intro _environment _order _Reference _input _valid _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro environment _order Reference input _valid _initialized
    have restored := code_borrowedRestored spec t environment
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code spec t).BorrowedRestored Reference input.state
      ((code spec t).execute environment Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
      (fun _ => rfl) _ _
  · intro _environment _order _Reference _input _valid _initialized path _supported
    exact code_events_le spec t path
  · intro _environment _order _Reference _input _valid _initialized path _supported
    exact code_resident_le spec t path
  · intro _environment _order _Reference _input _valid _initialized path _supported
    exact code_auxiliary_le spec t path
  · intro _environment _order _Reference _input _valid _initialized path _supported
    apply (Circuit.quantumTime_le_unitDepth _ _).trans
    exact code_depth_le spec t path

/-- One fixed sample-and-recovery program solves every admitted source and true order. -/
public theorem main {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (x t : Nat) :
    ∃ candidate : Algorithm (Sampling.Native.Framed.model t width)
        (pre width) (post t width) (outputShape t),
      Algorithm.Solves candidate (problem spec x t) :=
  ⟨algorithm spec t, algorithm_solves spec x t⟩

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
