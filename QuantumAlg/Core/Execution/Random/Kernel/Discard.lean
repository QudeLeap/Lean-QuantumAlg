/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Random.Kernel
public import QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Random.Kernel
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Forgetting finite stochastic outcomes

Summing a sampled outcome restores each original classical record together
with its complete quantum-reference block. The distribution may depend on
that record and need not be uniform. This mathematical observation does not
reset the actual hidden state or release any caller-addressable storage.
-/

namespace QuantumAlg.Execution

noncomputable section

/-- Summing a normalized finite transition preserves every complete original block. -/
public theorem kernelChoice_map_fst {C Outcome : Type} [Fintype C] [Fintype Outcome]
    [DecidableEq C] {R : Register} (state : ExecutionState C R)
    (transition : C → PMF Outcome) :
    (kernelChoice state transition).mapClassical Prod.fst = state := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [ExecutionState.mapClassical_block_matrix, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single result]
  · simp only [kernelChoice_block_matrix, if_true]
    rw [← Finset.sum_smul, finite_probability_sum, one_smul]
  · intro other _ different
    simp only [if_neg different, Finset.sum_const_zero]
  · intro absent
    exact (absent (Finset.mem_univ result)).elim

/-- Observations of the original record retain all correlations after summing actual outcomes. -/
private theorem kernelChoice_map_ignore_proof {C D Outcome : Type}
    [Fintype C] [Fintype D] [Fintype Outcome] [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (transition : C → PMF Outcome) (update : C → D) :
    (kernelChoice state transition).mapClassical (fun entry => update entry.1) =
      state.mapClassical update := by
  classical
  exact (ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance) (kernelChoice state transition) Prod.fst update).symm.trans
      (congrArg (fun prior => prior.mapClassical update) (kernelChoice_map_fst state transition))

/-- Outcome forgetting preserves observations for both chosen equality-decision implementations. -/
public theorem kernelChoice_map_ignore {C D Outcome : Type}
    [Fintype C] [Fintype D] [Fintype Outcome]
    {beforeMap afterMap : DecidableEq D} {R : Register}
    (state : ExecutionState C R) (transition : C → PMF Outcome) (update : C → D) :
    @ExecutionState.mapClassical (C × Outcome) D _ _ R beforeMap
        (kernelChoice state transition) (fun entry => update entry.1) =
      @ExecutionState.mapClassical C D _ _ R afterMap state update :=
  (@kernelChoice_map_ignore_proof C D Outcome _ _ _ beforeMap R state transition update).trans
    (ExecutionState.executionState_mapClassical_congr state rfl)

end

end QuantumAlg.Execution
