/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Borrowed.Embedding.Restoration
import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Composition.Laws

/-!
# Complete borrowed restoration under service-aware parallel execution

Service coordinate changes only regroup mathematical history and retain both
persistent service states. Each physical child restores the caller's complete
borrowed observation through the exact embedding theorem. Their actual
sequential interpreter composition therefore restores the same joint CQ state,
without assuming independent caller or service inputs.
-/

namespace QuantumAlg

noncomputable section

attribute [local instance] Classical.decEq

namespace Execution

private lemma observeBorrowed_map_decisions
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    {H K : Type} [Fintype H] [Fintype K]
    {decision : DecidableEq (Store ctx × K)}
    (state : State ctx Reference H) (update : Store ctx × H → Store ctx × K)
    (preserves : ∀ value,
      (update value).1.readBorrowedClassical = value.1.readBorrowedClassical) :
    observeBorrowed Reference
        (@ExecutionState.mapClassical _ _ _ _ _ decision state update) =
      observeBorrowed Reference state := by
  refine Eq.trans ?_ (observeBorrowed_mapClassical state update preserves)
  exact congrArg (fun current : State ctx Reference K => observeBorrowed Reference current)
    (ExecutionState.executionState_mapClassical_congr state rfl)

variable {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {History Path : Type} [Fintype History] [Fintype Path]

/-- Selecting the left persistent service preserves the entire borrowed observation. -/
lemma observeBorrowed_serviceInputLeft
    (state : State ctx Reference (parent.HiddenState × History)) :
    observeBorrowed Reference (serviceInputLeft join state) =
      observeBorrowed Reference state := by
  dsimp only [serviceInputLeft]
  exact observeBorrowed_map_decisions state
    ((Equiv.refl (Store ctx)).prodCongr (serviceHistoryLeft join History)) (fun _ => rfl)

/-- Selecting the right persistent service preserves the entire borrowed observation. -/
lemma observeBorrowed_serviceInputRight
    (state : State ctx Reference (parent.HiddenState × History)) :
    observeBorrowed Reference (serviceInputRight join state) =
      observeBorrowed Reference state := by
  dsimp only [serviceInputRight]
  exact observeBorrowed_map_decisions state
    ((Equiv.refl (Store ctx)).prodCongr (serviceHistoryRight join History)) (fun _ => rfl)

/-- Returning the left service and its actual path changes no borrowed coordinate. -/
lemma observeBorrowed_serviceOutputLeft
    (state : State ctx Reference (left.HiddenState × ((right.HiddenState × History) × Path))) :
    observeBorrowed Reference (serviceOutputLeft join state) =
      observeBorrowed Reference state := by
  dsimp only [serviceOutputLeft]
  exact observeBorrowed_map_decisions state
    ((Equiv.refl (Store ctx)).prodCongr (serviceResultLeft join History Path).symm)
    (fun _ => rfl)

/-- Returning the right service and its actual path changes no borrowed coordinate. -/
lemma observeBorrowed_serviceOutputRight
    (state : State ctx Reference (right.HiddenState × ((left.HiddenState × History) × Path))) :
    observeBorrowed Reference (serviceOutputRight join state) =
      observeBorrowed Reference state := by
  dsimp only [serviceOutputRight]
  exact observeBorrowed_map_decisions state
    ((Equiv.refl (Store ctx)).prodCongr (serviceResultRight join History Path).symm)
    (fun _ => rfl)

end Execution

namespace Circuit

open Execution

/-- The two actual classical children restore one complete borrowed caller observation. -/
lemma borrowedRestored_parallelClassical
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical} {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.classical operations leftService) left left false)
    (second : Circuit (.classical operations rightService) right right false)
    (environment : (ExecutionModel.classical operations parentService).Environment)
    (firstRestores : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State left Reference (leftService.HiddenState × History)),
      first.BorrowedRestored Reference state (first.execute
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference state))
    (secondRestores : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State right Reference (rightService.HiddenState × History)),
      second.BorrowedRestored Reference state (second.execute
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference state))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × History)) :
    (Circuit.parallelClassical (allowAllocation := allowAllocation)
      join separate first second).BorrowedRestored Reference state
      ((Circuit.parallelClassical (allowAllocation := allowAllocation)
        join separate first second).execute environment Reference state) := by
  let firstCall : Circuit (.classical operations leftService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnion left right separate) first
  let secondCall : Circuit (.classical operations rightService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnionRight left right separate) second
  let leftResult := firstCall.execute
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
    Reference (serviceInputLeft join state)
  let afterLeft := serviceOutputLeft join leftResult
  have firstSame : observeBorrowed Reference afterLeft = observeBorrowed Reference state := by
    have restored := borrowedRestored_embed (allowAllocation := false)
      (model := .classical operations leftService)
      (ContextEmbedding.alongUnion left right separate) first
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ firstRestores
      Reference (serviceInputLeft join state)
    have restored' : observeBorrowed Reference leftResult =
        observeBorrowed Reference (serviceInputLeft join state) := restored
    exact (observeBorrowed_serviceOutputLeft join leftResult).trans
      (restored'.trans (observeBorrowed_serviceInputLeft join state))
  let rightResult := secondCall.execute
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
    Reference (serviceInputRight join afterLeft)
  let afterRight := serviceOutputRight join rightResult
  have secondSame : observeBorrowed Reference afterRight =
      observeBorrowed Reference afterLeft := by
    have restored := borrowedRestored_embed (allowAllocation := false)
      (model := .classical operations rightService)
      (ContextEmbedding.alongUnionRight left right separate) second
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ secondRestores
      Reference (serviceInputRight join afterLeft)
    have restored' : observeBorrowed Reference rightResult =
        observeBorrowed Reference (serviceInputRight join afterLeft) := restored
    exact (observeBorrowed_serviceOutputRight join rightResult).trans
      (restored'.trans (observeBorrowed_serviceInputRight join afterLeft))
  rw [BorrowedRestored, observeBorrowedAfter_sameContext, circuit_execute_parallelClassical]
  exact (observeBorrowed_map_decisions afterRight
    (fun record =>
      (record.1, (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2)))))
    (fun _ => rfl)).trans (secondSame.trans firstSame)

/-- The two actual quantum children restore the same complete correlated borrowed interface. -/
lemma borrowedRestored_parallelQuantum
    {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum} {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Circuit (.quantum gates oracles operations leftService) left left false)
    (second : Circuit (.quantum gates oracles operations rightService) right right false)
    (environment : (ExecutionModel.quantum gates oracles operations parentService).Environment)
    (firstRestores : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State left Reference (leftService.HiddenState × History)),
      first.BorrowedRestored Reference state (first.execute
        ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference state))
    (secondRestores : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State right Reference (rightService.HiddenState × History)),
      second.BorrowedRestored Reference state (second.execute
        ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference state))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × History)) :
    (Circuit.parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).BorrowedRestored Reference state
      ((Circuit.parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).execute environment Reference state) := by
  let firstCall : Circuit (.quantum gates oracles operations leftService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnion left right separate) first
  let secondCall : Circuit (.quantum gates oracles operations rightService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed (ContextEmbedding.alongUnionRight left right separate) second
  let leftResult := firstCall.execute
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
    Reference (serviceInputLeft join state)
  let afterLeft := serviceOutputLeft join leftResult
  have firstSame : observeBorrowed Reference afterLeft = observeBorrowed Reference state := by
    have restored := borrowedRestored_embed (allowAllocation := false)
      (model := .quantum gates oracles operations leftService)
      (ContextEmbedding.alongUnion left right separate) first
      ⟨environment.quantum, join.interpretationLeft environment.classical⟩ firstRestores
      Reference (serviceInputLeft join state)
    have restored' : observeBorrowed Reference leftResult =
        observeBorrowed Reference (serviceInputLeft join state) := restored
    exact (observeBorrowed_serviceOutputLeft join leftResult).trans
      (restored'.trans (observeBorrowed_serviceInputLeft join state))
  let rightResult := secondCall.execute
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
    Reference (serviceInputRight join afterLeft)
  let afterRight := serviceOutputRight join rightResult
  have secondSame : observeBorrowed Reference afterRight =
      observeBorrowed Reference afterLeft := by
    have restored := borrowedRestored_embed (allowAllocation := false)
      (model := .quantum gates oracles operations rightService)
      (ContextEmbedding.alongUnionRight left right separate) second
      ⟨environment.quantum, join.interpretationRight environment.classical⟩ secondRestores
      Reference (serviceInputRight join afterLeft)
    have restored' : observeBorrowed Reference rightResult =
        observeBorrowed Reference (serviceInputRight join afterLeft) := restored
    exact (observeBorrowed_serviceOutputRight join rightResult).trans
      (restored'.trans (observeBorrowed_serviceInputRight join afterLeft))
  rw [BorrowedRestored, observeBorrowedAfter_sameContext, circuit_execute_parallelQuantum]
  exact (observeBorrowed_map_decisions afterRight
    (fun record =>
      (record.1, (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2)))))
    (fun _ => rfl)).trans (secondSame.trans firstSame)

end Circuit

end

end QuantumAlg
