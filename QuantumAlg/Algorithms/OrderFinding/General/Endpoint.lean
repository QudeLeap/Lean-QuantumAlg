/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.OrderFinding.General.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.Execution
import all QuantumAlg.Algorithms.OrderFinding.General.Success
import all QuantumAlg.Algorithms.OrderFinding.General.Restoration
import all QuantumAlg.Algorithms.OrderFinding.General.Resources
import all QuantumAlg.Algorithms.OrderFinding.General.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution

/-!
# Complete native general order finding on the original source domain

The actual source circuit writes its measured bits, then finite native
continued-fraction recovery reads those same bits and the borrowed base.
The complete run returns the original optional order candidate, satisfies
the original success bound and restores all borrowed correlations. Its
event, depth and space bounds describe this same execution.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Validity retains exactly the original supported canonical base and source register window. -/
public theorem problem_valid_iff {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width)
    (state : ExecutionState (Execution.Store (pre width)) (pre width).register) :
    (problem hinput A).valid state ↔
      (∀ store, 0 < (state.block store).mass →
        store.read (baseSourceRef width) =
          .canonicalResidue ⟨x % N, lt_of_lt_of_le (Nat.mod_lt x A.modulus_pos)
            A.register_fits⟩) ∧ 0 < t ∧ N ^ 2 ≤ 2 ^ t ∧ 2 ^ t < 2 * N ^ 2 := Iff.rfl

/-- Execute original source sampling and native recovery with complete live Output. -/
public def algorithm {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) :
    Algorithm .quantum (pre width) (post t width) (.option (.unsignedWord (t + 1))) where
  run := NativeEndpoint.run hinput A

private theorem actual_success {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width)
    {Reference : Register} (input : Execution.Input (pre width) Reference)
    (valid : HasCanonicalBase hinput A input.localState)
    (hregister : N ^ 2 ≤ 2 ^ t) (hupper : 2 ^ t < 2 * N ^ 2) :
    (successLB r).value ≤
      ((NativeEndpoint.run hinput A).relationalDistribution input).toOuterMeasure
        {pair | (problem hinput A).accepts pair.1 pair.2} := by
  have projection :
      ((NativeEndpoint.run hinput A).relationalDistribution input).toOuterMeasure
          {pair | (problem hinput A).accepts pair.1 pair.2} =
        ((NativeEndpoint.run hinput A).outputDistribution input).toOuterMeasure
          {output | SuccessfulOutcome r output} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection]
  exact NativeEndpoint.output_successProbability_ge hinput A input valid hregister hupper

/-- The full actual run solves general order finding with the original success and input window. -/
public theorem main {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) :
    ∃ candidate :
        Algorithm .quantum (pre width) (post t width) (.option (.unsignedWord (t + 1))),
      Algorithm.Solves candidate (problem hinput A) := by
  refine ⟨algorithm hinput A, ?_⟩
  constructor
  · intro Reference input valid
    rcases valid with ⟨canonical, _positiveWidth, hregister, hupper⟩
    simp only [Algorithm.relationalDistribution, algorithm]
    dsimp only [post]
    exact actual_success hinput A input canonical hregister hupper
  · intro _Reference _input _valid requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _valid
    exact NativeEndpoint.code_borrowedRestored hinput A
      (input.state.mapClassical (fun store => (store, store)))
  · intro _Reference _input _valid path _supported
    exact NativeEndpoint.code_events_le hinput A path
  · intro _Reference _input _valid path _supported
    exact NativeEndpoint.code_resident_le hinput A path
  · intro _Reference _input _valid path _supported
    exact NativeEndpoint.code_auxiliary_le hinput A path
  · intro _Reference _input _valid path _supported
    exact NativeEndpoint.code_depth_le hinput A path

end

end QuantumAlg.OrderFinding.ShorSourceJoint
