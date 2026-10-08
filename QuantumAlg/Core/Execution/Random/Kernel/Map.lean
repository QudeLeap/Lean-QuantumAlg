/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Random.Kernel
public import QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Stochastic kernels through classical history maps

The declared distribution is evaluated at the actual mapped record. Colliding
records contribute their full weighted blocks, so these equations do not need
injective maps, independent distributions or normalized conditional branches.
-/

namespace QuantumAlg.Execution

noncomputable section

/-- Applying a kernel after grouping records equals grouping the correspondingly sampled records. -/
private theorem kernelChoice_mapClassical_proof {C D Outcome : Type}
    [Fintype C] [Fintype D] [Fintype Outcome] [DecidableEq D] [DecidableEq (D × Outcome)]
    {R : Register} (state : ExecutionState C R) (update : C → D)
    (transition : D → PMF Outcome) :
    kernelChoice (state.mapClassical update) transition =
      (kernelChoice state (transition ∘ update)).mapClassical
        (fun entry => (update entry.1, entry.2)) := by
  classical
  apply ExecutionState.ext
  rintro ⟨result, outcome⟩
  apply DensityOperator.ext
  rw [kernelChoice_block_matrix, ExecutionState.mapClassical_block_matrix,
    ExecutionState.mapClassical_block_matrix, Fintype.sum_prod_type, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro entry _
  by_cases selected : update entry = result
  · simp [selected, kernelChoice_block_matrix]
  · simp [selected]

/-- Grouping and sampling commute for the chosen finite equality-decision implementations. -/
public theorem kernelChoice_mapClassical {C D Outcome : Type}
    [Fintype C] [Fintype D] [Fintype Outcome]
    {beforeMap : DecidableEq D} {afterMap : DecidableEq (D × Outcome)}
    {R : Register} (state : ExecutionState C R) (update : C → D)
    (transition : D → PMF Outcome) :
    kernelChoice (@ExecutionState.mapClassical C D _ _ R beforeMap state update) transition =
      @ExecutionState.mapClassical (C × Outcome) (D × Outcome) _ _ R afterMap
        (kernelChoice state (transition ∘ update))
        (fun entry => (update entry.1, entry.2)) :=
  @kernelChoice_mapClassical_proof C D Outcome _ _ _ beforeMap afterMap R state update transition

end

end QuantumAlg.Execution
