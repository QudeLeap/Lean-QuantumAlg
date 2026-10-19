/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.ClassicalTag.Embedding
import all QuantumAlg.Core.Execution.Composition.ClassicalTag.Service

/-!
# Reference-tag slices through disjoint parallel interpretation

Both physical frames and inactive service states remain present through the
two actual recursive calls. The complete output retains the original history,
its tag and the pair of actual child paths, including correlated input states.
-/

namespace QuantumAlg.Execution

noncomputable section

private lemma pairPaths_eq_mapHistory
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    {Hidden H LeftPath RightPath : Type}
    [Fintype Hidden] [Fintype H] [Fintype LeftPath] [Fintype RightPath]
    {decision : DecidableEq (Store ctx × (Hidden × (H × (LeftPath × RightPath))))}
    (state : State ctx Reference (Hidden × ((H × LeftPath) × RightPath))) :
    @ExecutionState.mapClassical _ _ _ _ _ decision state
        (fun record =>
          (record.1, (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2))))) =
      state.mapHistory
        (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
  ExecutionState.executionState_mapClassical_congr state rfl

/-- Actual disjoint composition preserves every original tag and both recorded paths. -/
lemma parallelPreserving_tagNatural
    {left right parent : ClassicalOracleModel}
    (join : ClassicalOracleModel.ServiceJoin left right parent)
    {kind : ProblemKind} {leftCtx rightCtx : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx)
    {LeftPath RightPath : Type} [Fintype LeftPath] [Fintype RightPath]
    (first : (Reference : Register) →
      Preserving left.HiddenState leftCtx leftCtx Reference LeftPath)
    (second : (Reference : Register) →
      Preserving right.HiddenState rightCtx rightCtx Reference RightPath)
    (firstTag : TagNatural first) (secondTag : TagNatural second)
    (firstHistory : ∀ Reference, HistoryNatural (first Reference))
    (secondHistory : ∀ Reference, HistoryNatural (second Reference))
    (firstReference : ReferenceNatural first) (secondReference : ReferenceNatural second) :
    TagNatural (fun Reference => parallelPreserving join separate
      (first (rightCtx.register.prod Reference))
      (second (leftCtx.register.prod Reference))) := by
  let leftPlacement := ContextEmbedding.alongUnion leftCtx rightCtx separate
  let rightPlacement := ContextEmbedding.alongUnionRight leftCtx rightCtx separate
  let leftBody : (Reference : Register) →
      Preserving parent.HiddenState (leftCtx.disjointUnion rightCtx separate)
        (leftCtx.disjointUnion rightCtx separate) Reference LeftPath :=
    fun Reference => embedServiceLeftPreserving join leftPlacement
      (first (rightCtx.register.prod Reference))
  let rightBody : (Reference : Register) →
      Preserving parent.HiddenState (leftCtx.disjointUnion rightCtx separate)
        (leftCtx.disjointUnion rightCtx separate) Reference RightPath :=
    fun Reference => embedServiceRightPreserving join rightPlacement
      (second (leftCtx.register.prod Reference))
  have rightHistory : ∀ Reference, HistoryNatural (rightBody Reference) := fun Reference =>
    serviceRightPreserving_history join _
      (embedPreserving_history rightPlacement Reference _ (secondHistory _))
  have leftTag : TagNatural leftBody := serviceLeftPreserving_tagNatural join _
    (embedPreserving_tagNatural leftPlacement first firstTag firstHistory firstReference)
    (fun Reference => embedPreserving_history leftPlacement Reference _ (firstHistory _))
  have rightTag : TagNatural rightBody := serviceRightPreserving_tagNatural join _
    (embedPreserving_tagNatural rightPlacement second secondTag secondHistory secondReference)
    (fun Reference => embedPreserving_history rightPlacement Reference _ (secondHistory _))
  intro Reference Tag H _ state
  dsimp only [parallelPreserving]
  rw [pairPaths_eq_mapHistory, pairPaths_eq_mapHistory]
  exact sequence_tagNatural leftBody rightBody leftTag rightTag rightHistory state

end

end QuantumAlg.Execution
