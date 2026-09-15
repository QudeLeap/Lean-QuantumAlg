/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Random.Map

/-!
# Complete store blocks under actual classical processing

Grouping finite histories commutes with a transformation of the actual
store. An independent uniform choice similarly retains each old complete
store block with its actual uniform coefficient before the real store map.
These identities preserve every quantum-reference matrix entry, so seed
invariants can pass through actual allocations and samplers. Independence
belongs to the existing uniform instruction and imposes no restriction on
the incoming store, quantum systems or reference correlations.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A map of real stores groups exactly their old complete density blocks. -/
theorem mapStore_block_matrix {C D H K : Type}
    [Fintype C] [Fintype D] [Fintype H] [Fintype K] {R : Register}
    (state : ExecutionState (C × H) R) (storeMap : C → D) (historyMap : C × H → K)
    (result : D) :
    (((state.mapClassical (fun entry => (storeMap entry.1, historyMap entry))).mapClassical
      (fun entry => entry.1)).block result).matrix =
      ∑ original : C, if storeMap original = result then
        ((state.mapClassical (fun entry => entry.1)).block original).matrix else 0 := by
  have first := ExecutionState.executionState_mapClassical_comp state
    (fun entry => (storeMap entry.1, historyMap entry)) (fun entry => entry.1)
  have second := ExecutionState.executionState_mapClassical_comp state
    (fun entry => entry.1) storeMap
  exact congrArg (fun output : ExecutionState D R => (output.block result).matrix)
    (first.trans second.symm)

/-- An actual uniform choice and store update retain each old block with its genuine coefficient. -/
theorem sampledMap_store_matrix {C D H K : Type}
    [Fintype C] [Fintype D] [Fintype H] [Fintype K] {R : Register}
    (state : ExecutionState (C × H) R) (count : ℕ+)
    (storeMap : C → Fin count → D) (historyMap : (C × H) × Fin count → K) (result : D) :
    ((((uniformChoice state count).mapClassical
      (fun entry => (storeMap entry.1.1 entry.2, historyMap entry))).mapClassical
        (fun entry => entry.1)).block result).matrix =
      ∑ original : C, ∑ choice : Fin count, if storeMap original choice = result then
        (count : ℝ)⁻¹ • ((state.mapClassical (fun entry => entry.1)).block original).matrix
      else 0 := by
  let drawn := uniformChoice state count
  let update := fun entry : (C × H) × Fin count =>
    (storeMap entry.1.1 entry.2, historyMap entry)
  let group := fun entry : (C × H) × Fin count => (entry.1.1, entry.2)
  let read := fun entry : C × Fin count => storeMap entry.1 entry.2
  have first := ExecutionState.executionState_mapClassical_comp drawn update (fun entry => entry.1)
  have second := ExecutionState.executionState_mapClassical_comp drawn group read
  have grouped := uniformChoice_mapClassical state count (fun entry => entry.1)
  have actual := congrArg (fun output : ExecutionState D R => (output.block result).matrix)
    (first.trans (second.symm.trans
      (congrArg (fun output : ExecutionState (C × Fin count) R => output.mapClassical read)
        grouped.symm)))
  refine actual.trans ?_
  change (∑ entry : C × Fin count, if read entry = result then
    ((uniformChoice (state.mapClassical (fun entry => entry.1)) count).block entry).matrix
      else 0) = _
  rw [Fintype.sum_prod_type]
  simp only [uniformChoice_block_matrix, read]

end

end QuantumAlg.Execution.BasisSeeded
