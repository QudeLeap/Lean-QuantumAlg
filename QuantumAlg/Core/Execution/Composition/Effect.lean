/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Composition.Embedding
import all QuantumAlg.Core.Execution.Interpret.Preserving
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.State.Effect
import all QuantumAlg.Core.Base.Gate.Effect.Embedding

/-!
# Certified observations through complete physical and service composition

The observable is pulled through the same store correspondence and physical
basis equivalence as the actual interpreter. Every matrix remains a positive
contraction; the complement and external reference are both retained.
-/

namespace QuantumAlg

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

/-- Exact basis transport pulls an observable back by the same basis equivalence. -/
lemma effectWeight_reindex {C : Type} [Fintype C] {R S : Register}
    (state : ExecutionState C R) (basis : R.Index ≃ S.Index) (effects : C → Effect S) :
    (state.reindex basis).effectWeight effects =
      state.effectWeight (fun original =>
        Effect.compress basis basis.injective (effects original)) := by
  unfold effectWeight
  apply Finset.sum_congr rfl
  intro original _
  unfold Effect.weight
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Effect.compress_matrix,
    Matrix.submatrix_apply, reindex_block_entry]
  rw [← basis.sum_comp]
  apply Finset.sum_congr rfl
  intro row _
  rw [← basis.sum_comp]
  simp only [Equiv.symm_apply_apply]

end ExecutionState

namespace ContextEmbedding

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) (Reference : Register)

/-- Pull an observable through the exact splitting coordinates. -/
def splitEffectPullback {H : Type}
    (effects : Store localCtx × (Store placement.frame × H) →
      Effect (Register.prod localCtx.register (Register.prod placement.frame.register Reference)))
    (original : Store caller × H) : Effect (Register.prod caller.register Reference) :=
  Effect.compress (placement.referenceBasis Reference)
    (placement.referenceBasis Reference).injective
    (effects (placement.record H original))

/-- Pull an observable through the inverse of the exact splitting coordinates. -/
def joinEffectPullback {H : Type}
    (effects : Store caller × H → Effect (Register.prod caller.register Reference))
    (original : Store localCtx × (Store placement.frame × H)) :
    Effect (Register.prod localCtx.register (Register.prod placement.frame.register Reference)) :=
  Effect.compress (placement.referenceBasis Reference).symm
    (placement.referenceBasis Reference).symm.injective
    (effects ((placement.record H).symm original))

/-- Splitting preserves the exact trace pairing, including every reference correlation. -/
lemma effectWeight_split {H : Type} [Fintype H]
    (state : State caller Reference H)
    (effects : Store localCtx × (Store placement.frame × H) →
      Effect (Register.prod localCtx.register (Register.prod placement.frame.register Reference))) :
    (placement.split state).effectWeight effects =
      state.effectWeight (placement.splitEffectPullback Reference effects) := by
  unfold split
  rw [ExecutionState.effectWeight_reindex, ExecutionState.effectWeight_mapClassical_decision]
  rfl

/-- Rejoining preserves the exact trace pairing for the complete caller observable. -/
lemma effectWeight_join {H : Type} [Fintype H]
    (state : State localCtx (Register.prod placement.frame.register Reference)
      (Store placement.frame × H))
    (effects : Store caller × H → Effect (Register.prod caller.register Reference)) :
    (placement.join state).effectWeight effects =
      state.effectWeight (placement.joinEffectPullback Reference effects) := by
  unfold join
  rw [ExecutionState.effectWeight_reindex, ExecutionState.effectWeight_mapClassical_decision]
  rfl

end ContextEmbedding

namespace Execution

/-- A backward observable family for one original recursive interpretation. -/
abbrev EffectPullback {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (Reference : Register) (Hidden Path : Type) :=
  ∀ {H : Type},
    (Store ctx × (Hidden × (H × Path)) → Effect (Register.prod ctx.register Reference)) →
      (Store ctx × (Hidden × H) → Effect (Register.prod ctx.register Reference))

/-- Exact agreement of a recursive interpretation with its backward observable. -/
abbrev EffectNatural {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {Hidden Path : Type} [Fintype Hidden] [Fintype Path]
    (body : Preserving Hidden ctx ctx Reference Path)
    (pullback : EffectPullback ctx Reference Hidden Path) : Prop :=
  ∀ {H : Type} [Fintype H] (state : State ctx Reference (Hidden × H)) effects,
    (body state).val.effectWeight effects = state.effectWeight (pullback effects)

/-- Pull through the original child, with both complete coordinate changes retained. -/
def embedEffectPullback {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
    {Hidden Path : Type} (placement : ContextEmbedding localCtx caller) (Reference : Register)
    (body : EffectPullback localCtx
      (Register.prod placement.frame.register Reference) Hidden Path) :
    EffectPullback caller Reference Hidden Path := fun effects =>
  placement.splitEffectPullback Reference (fun original =>
    body (fun result => placement.joinEffectPullback Reference effects
      (result.1, (result.2.2.1.1,
        (result.2.1, (result.2.2.1.2, result.2.2.2)))))
      (original.1, (original.2.2.1, (original.2.1, original.2.2.2))))

/-- Physical framing preserves the complete mixed-state observation equation. -/
lemma embedPreserving_effect {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
    {Hidden Path : Type} [Fintype Hidden] [Fintype Path]
    (placement : ContextEmbedding localCtx caller) (Reference : Register)
    (body : Preserving Hidden localCtx localCtx
      (Register.prod placement.frame.register Reference) Path)
    (pullback : EffectPullback localCtx
      (Register.prod placement.frame.register Reference) Hidden Path)
    (natural : EffectNatural body pullback) :
    EffectNatural (embedPreserving placement Reference body)
      (embedEffectPullback placement Reference pullback) := by
  intro H _ state effects
  dsimp only [embedPreserving]
  rw [placement.effectWeight_join]
  unfold State.mapHistory
  rw [ExecutionState.effectWeight_mapClassical_decision, natural,
    ExecutionState.effectWeight_mapClassical_decision, placement.effectWeight_split]
  rfl

variable {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register} {Path : Type}

/-- The inactive right hidden state is an unchanged observable argument. -/
def serviceEffectLeft (body : EffectPullback ctx Reference left.HiddenState Path) :
    EffectPullback ctx Reference parent.HiddenState Path := fun {H} effects original =>
  body (fun result => effects (result.1, (serviceResultLeft join H Path).symm result.2))
    (original.1, serviceHistoryLeft join H original.2)

/-- The inactive left hidden state is an unchanged observable argument. -/
def serviceEffectRight (body : EffectPullback ctx Reference right.HiddenState Path) :
    EffectPullback ctx Reference parent.HiddenState Path := fun {H} effects original =>
  body (fun result => effects (result.1, (serviceResultRight join H Path).symm result.2))
    (original.1, serviceHistoryRight join H original.2)

/-- Left service selection preserves the actual observable pullback. -/
lemma serviceLeftPreserving_effect [Fintype Path]
    (body : Preserving left.HiddenState ctx ctx Reference Path)
    (pullback : EffectPullback ctx Reference left.HiddenState Path)
    (natural : EffectNatural body pullback) :
    EffectNatural (serviceLeftPreserving join body) (serviceEffectLeft join pullback) := by
  intro H _ state effects
  dsimp only [serviceLeftPreserving, serviceOutputLeft]
  rw [ExecutionState.effectWeight_mapClassical_decision, natural]
  unfold serviceInputLeft
  rw [ExecutionState.effectWeight_mapClassical_decision]
  rfl

/-- Right service selection preserves the actual observable pullback. -/
lemma serviceRightPreserving_effect [Fintype Path]
    (body : Preserving right.HiddenState ctx ctx Reference Path)
    (pullback : EffectPullback ctx Reference right.HiddenState Path)
    (natural : EffectNatural body pullback) :
    EffectNatural (serviceRightPreserving join body) (serviceEffectRight join pullback) := by
  intro H _ state effects
  dsimp only [serviceRightPreserving, serviceOutputRight]
  rw [ExecutionState.effectWeight_mapClassical_decision, natural]
  unfold serviceInputRight
  rw [ExecutionState.effectWeight_mapClassical_decision]
  rfl

/-- Parallel observations are pulled backward through the actual right and left calls. -/
def parallelEffectPullback {leftCtx rightCtx : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx) (Reference : Register)
    {LeftPath RightPath : Type}
    (first : EffectPullback leftCtx (Register.prod rightCtx.register Reference)
      left.HiddenState LeftPath)
    (second : EffectPullback rightCtx (Register.prod leftCtx.register Reference)
      right.HiddenState RightPath) :
    EffectPullback (leftCtx.disjointUnion rightCtx separate) Reference
      parent.HiddenState (LeftPath × RightPath) := fun effects =>
  serviceEffectLeft join
    (embedEffectPullback (ContextEmbedding.alongUnion leftCtx rightCtx separate) Reference first)
    (serviceEffectRight join
      (embedEffectPullback (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
        Reference second)
      (fun result => effects
        (result.1, (result.2.1, (result.2.2.1.1, (result.2.2.1.2, result.2.2.2))))))

/-- Both services retain the exact complete observation law on correlated inputs. -/
lemma parallelPreserving_effect {leftCtx rightCtx : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx)
    {LeftPath RightPath : Type} [Fintype LeftPath] [Fintype RightPath]
    (first : Preserving left.HiddenState leftCtx leftCtx
      (Register.prod rightCtx.register Reference) LeftPath)
    (second : Preserving right.HiddenState rightCtx rightCtx
      (Register.prod leftCtx.register Reference) RightPath)
    (firstPullback : EffectPullback leftCtx (Register.prod rightCtx.register Reference)
      left.HiddenState LeftPath)
    (secondPullback : EffectPullback rightCtx (Register.prod leftCtx.register Reference)
      right.HiddenState RightPath)
    (firstNatural : EffectNatural first firstPullback)
    (secondNatural : EffectNatural second secondPullback) :
    EffectNatural (parallelPreserving join separate first second)
      (parallelEffectPullback join separate Reference firstPullback secondPullback) := by
  have leftNatural : EffectNatural (serviceLeftPreserving join
      (embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate) Reference first))
      (serviceEffectLeft join
        (embedEffectPullback (ContextEmbedding.alongUnion leftCtx rightCtx separate)
          Reference firstPullback)) := serviceLeftPreserving_effect join _ _
    (embedPreserving_effect (ContextEmbedding.alongUnion leftCtx rightCtx separate)
      Reference first firstPullback firstNatural)
  have rightNatural : EffectNatural (serviceRightPreserving join
      (embedPreserving (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
        Reference second))
      (serviceEffectRight join
        (embedEffectPullback (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
          Reference secondPullback)) := serviceRightPreserving_effect join _ _
    (embedPreserving_effect (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
      Reference second secondPullback secondNatural)
  intro H _ state effects
  dsimp only [parallelPreserving, embedServiceLeftPreserving, embedServiceRightPreserving]
  rw [ExecutionState.effectWeight_mapClassical_decision, rightNatural, leftNatural]
  rfl

end Execution

end

end QuantumAlg
