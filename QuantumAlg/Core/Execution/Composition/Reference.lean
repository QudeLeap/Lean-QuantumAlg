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
import all QuantumAlg.Core.Execution.Composition.Coordinates

/-!
# External-reference naturality of complete physical and service composition

The child's external reference includes the entire physical complement.
Changing the original external-reference basis leaves all complement systems,
classical cells, persistent services and their joint density blocks intact.
-/

namespace QuantumAlg

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ContextEmbedding

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) {Reference Other : Register}
  (basis : Reference.Index ≃ Other.Index) {H : Type} [Fintype H]

/-- The complete physical split commutes with a change of the original reference basis. -/
lemma split_reference (state : State caller Reference H) :
    placement.split (state.reindex (S := Register.prod caller.register Other)
      ((Equiv.refl caller.register.Index).prodCongr basis)) =
      (placement.split state).reindex
        (S := Register.prod localCtx.register (Register.prod placement.frame.register Other))
        ((Equiv.refl localCtx.register.Index).prodCongr
          ((Equiv.refl placement.frame.register.Index).prodCongr basis)) := by
  unfold split
  rw [ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.reindex_trans, ExecutionState.reindex_trans]
  congr 1

/-- The inverse physical coordinates retain the same external-reference correspondence. -/
lemma join_reference
    (state : State localCtx (Register.prod placement.frame.register Reference)
      (Store placement.frame × H)) :
    placement.join (state.reindex
      (S := Register.prod localCtx.register (Register.prod placement.frame.register Other))
      ((Equiv.refl localCtx.register.Index).prodCongr
        ((Equiv.refl placement.frame.register.Index).prodCongr basis))) =
      (placement.join state).reindex (S := Register.prod caller.register Other)
        ((Equiv.refl caller.register.Index).prodCongr basis) := by
  unfold join
  rw [ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.reindex_trans, ExecutionState.reindex_trans]
  congr 1

end ContextEmbedding

namespace Execution

/-- Naturality of an internal recursive interpretation in every external reference. -/
abbrev ReferenceNatural {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Hidden Path : Type} [Fintype Hidden] [Fintype Path]
    (body : (Reference : Register) → Preserving Hidden ctx ctx Reference Path) : Prop :=
  ∀ {Reference Other : Register} (basis : Reference.Index ≃ Other.Index)
    {H : Type} [Fintype H] (state : State ctx Reference (Hidden × H)),
    (body Other (state.reindex (S := Register.prod ctx.register Other)
      ((Equiv.refl ctx.register.Index).prodCongr basis))).val =
      (body Reference state).val.reindex (S := Register.prod ctx.register Other)
        ((Equiv.refl ctx.register.Index).prodCongr basis)

/-- Complete physical framing preserves arbitrary external-reference naturality. -/
lemma embedPreserving_reference {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
    {Hidden Path : Type} [Fintype Hidden] [Fintype Path]
    (placement : ContextEmbedding localCtx caller)
    (body : (Reference : Register) → Preserving Hidden localCtx localCtx Reference Path)
    (natural : ReferenceNatural body) :
    ReferenceNatural (fun Reference => embedPreserving placement Reference
      (body (Register.prod placement.frame.register Reference))) := by
  intro Reference Other basis H _ state
  dsimp only [embedPreserving]
  rw [placement.split_reference]
  rw [State.composition_reindex_mapHistory, natural,
    State.composition_reindex_mapHistory, placement.join_reference]

variable {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Path : Type} [Fintype Path]

/-- Left service routing changes only actual classical coordinates. -/
lemma serviceLeftPreserving_reference
    (body : (Reference : Register) → Preserving left.HiddenState ctx ctx Reference Path)
    (natural : ReferenceNatural body) :
    ReferenceNatural (fun Reference => serviceLeftPreserving join (body Reference)) := by
  intro Reference Other basis H _ state
  dsimp only [serviceLeftPreserving, serviceInputLeft, serviceOutputLeft]
  rw [ExecutionState.coordinate_reindex_mapClassical, natural,
    ExecutionState.coordinate_reindex_mapClassical]

/-- Right service routing changes only actual classical coordinates. -/
lemma serviceRightPreserving_reference
    (body : (Reference : Register) → Preserving right.HiddenState ctx ctx Reference Path)
    (natural : ReferenceNatural body) :
    ReferenceNatural (fun Reference => serviceRightPreserving join (body Reference)) := by
  intro Reference Other basis H _ state
  dsimp only [serviceRightPreserving, serviceInputRight, serviceOutputRight]
  rw [ExecutionState.coordinate_reindex_mapClassical, natural,
    ExecutionState.coordinate_reindex_mapClassical]

/-- Disjoint composition retains the original external-reference naturality in full. -/
lemma parallelPreserving_reference {leftCtx rightCtx : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx)
    {LeftPath RightPath : Type} [Fintype LeftPath] [Fintype RightPath]
    (first : (Reference : Register) →
      Preserving left.HiddenState leftCtx leftCtx Reference LeftPath)
    (second : (Reference : Register) →
      Preserving right.HiddenState rightCtx rightCtx Reference RightPath)
    (firstNatural : ReferenceNatural first) (secondNatural : ReferenceNatural second) :
    ReferenceNatural (fun Reference => parallelPreserving join separate
      (first (Register.prod rightCtx.register Reference))
      (second (Register.prod leftCtx.register Reference))) := by
  have leftNatural : ReferenceNatural (fun Reference => serviceLeftPreserving join
      (embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate)
        Reference (first (Register.prod rightCtx.register Reference)))) :=
    serviceLeftPreserving_reference join _
    (embedPreserving_reference (ContextEmbedding.alongUnion leftCtx rightCtx separate)
      first firstNatural)
  have rightNatural : ReferenceNatural (fun Reference => serviceRightPreserving join
      (embedPreserving (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
        Reference (second (Register.prod leftCtx.register Reference)))) :=
    serviceRightPreserving_reference join _
    (embedPreserving_reference (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
      second secondNatural)
  intro Reference Other basis H _ state
  dsimp only [parallelPreserving, embedServiceLeftPreserving, embedServiceRightPreserving]
  rw [leftNatural, rightNatural, ExecutionState.coordinate_reindex_mapClassical]

end Execution

end

end QuantumAlg
