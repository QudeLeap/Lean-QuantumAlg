/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.History.Selection.Native
import all QuantumAlg.Core.Execution.Composition.Parallel

/-!
# Complete history fibers through physical and service composition

The recursive hypotheses below concern the actual interpreter result functions.
They are discharged by circuit induction, never supplied by an algorithm caller.
The complement Store, quantum frame, inactive service and external Reference are
retained on both sides of every equality.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Complete physical placement preserves the initial-history selection law. -/
lemma embedPreserving_selectHistory {kind : ProblemKind}
    {localCtx caller : RuntimeCtx kind} {Hidden Path : Type}
    [Fintype Hidden] [Fintype Path] (placement : ContextEmbedding localCtx caller)
    (Reference : Register)
    (body : Preserving Hidden localCtx localCtx
      (Register.prod placement.frame.register Reference) Path)
    (natural : ∀ {H D : Type} [Fintype H] [DecidableEq D]
      (state : State localCtx (Register.prod placement.frame.register Reference) (Hidden × H))
      (read : H → D) (selected : D),
      (body state).val.selectHistory (fun record => read record.2.1) selected =
        (body (state.selectHistory (fun record => read record.2) selected)).val)
    {H D : Type} [Fintype H] [DecidableEq D]
    (state : State caller Reference (Hidden × H)) (read : H → D) (selected : D) :
    (embedPreserving placement Reference body state).val.selectHistory
        (fun record => read record.2.1) selected =
      (embedPreserving placement Reference body
        (state.selectHistory (fun record => read record.2) selected)).val := by
  let localInput := (placement.split state).mapHistory
    (fun record => (record.2.1, (record.1, record.2.2)))
  have input : localInput.selectHistory (fun record => read record.2.2) selected =
      (placement.split (state.selectHistory (fun record => read record.2) selected)).mapHistory
        (fun record => (record.2.1, (record.1, record.2.2))) := by
    dsimp only [localInput]
    rw [State.selectHistory_mapHistory]
    change ((placement.split state).selectHistory
      (fun record => read record.2.2) selected).mapHistory _ = _
    rw [placement.split_selectHistory state
      (fun record : Hidden × H => read record.2) selected]
  change (placement.join ((body localInput).val.mapHistory
    (fun record => (record.2.1.1, (record.1, (record.2.1.2, record.2.2)))))).selectHistory
      (fun record => read record.2.1) selected = _
  rw [placement.join_selectHistory, State.selectHistory_mapHistory]
  change placement.join (((body localInput).val.selectHistory
    (fun record => read record.2.1.2) selected).mapHistory _) = _
  rw [natural localInput (fun record : Store placement.frame × H => read record.2) selected,
    input]
  rfl

variable {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {Path : Type} [Fintype Path]

/-- Selecting the left service preserves each complete old-history fiber. -/
lemma serviceLeftPreserving_selectHistory
    (body : Preserving left.HiddenState ctx ctx Reference Path)
    (natural : ∀ {H D : Type} [Fintype H] [DecidableEq D]
      (state : State ctx Reference (left.HiddenState × H)) (read : H → D) (selected : D),
      (body state).val.selectHistory (fun record => read record.2.1) selected =
        (body (state.selectHistory (fun record => read record.2) selected)).val)
    {H D : Type} [Fintype H] [DecidableEq D]
    (state : State ctx Reference (parent.HiddenState × H)) (read : H → D) (selected : D) :
    (serviceLeftPreserving join body state).val.selectHistory
        (fun record => read record.2.1) selected =
      (serviceLeftPreserving join body
        (state.selectHistory (fun record => read record.2) selected)).val := by
  have input : (serviceInputLeft join state).selectHistory
      (fun record => read record.2.2) selected =
      serviceInputLeft join (state.selectHistory (fun record => read record.2) selected) := by
    dsimp only [serviceInputLeft, State.selectHistory]
    rw [ExecutionState.mapClassical_selectClassical]
    rfl
  have output (result : State ctx Reference
      (left.HiddenState × ((right.HiddenState × H) × Path))) :
      (serviceOutputLeft join result).selectHistory (fun record => read record.2.1) selected =
        serviceOutputLeft join
          (result.selectHistory (fun record => read record.2.1.2) selected) := by
    dsimp only [serviceOutputLeft, State.selectHistory]
    rw [ExecutionState.mapClassical_selectClassical]
    rfl
  change (serviceOutputLeft join (body (serviceInputLeft join state)).val).selectHistory
    (fun record => read record.2.1) selected = _
  rw [output, natural (serviceInputLeft join state)
    (fun record : right.HiddenState × H => read record.2) selected, input]
  rfl

/-- Selecting the right service preserves each complete old-history fiber. -/
lemma serviceRightPreserving_selectHistory
    (body : Preserving right.HiddenState ctx ctx Reference Path)
    (natural : ∀ {H D : Type} [Fintype H] [DecidableEq D]
      (state : State ctx Reference (right.HiddenState × H)) (read : H → D) (selected : D),
      (body state).val.selectHistory (fun record => read record.2.1) selected =
        (body (state.selectHistory (fun record => read record.2) selected)).val)
    {H D : Type} [Fintype H] [DecidableEq D]
    (state : State ctx Reference (parent.HiddenState × H)) (read : H → D) (selected : D) :
    (serviceRightPreserving join body state).val.selectHistory
        (fun record => read record.2.1) selected =
      (serviceRightPreserving join body
        (state.selectHistory (fun record => read record.2) selected)).val := by
  have input : (serviceInputRight join state).selectHistory
      (fun record => read record.2.2) selected =
      serviceInputRight join (state.selectHistory (fun record => read record.2) selected) := by
    dsimp only [serviceInputRight, State.selectHistory]
    rw [ExecutionState.mapClassical_selectClassical]
    rfl
  have output (result : State ctx Reference
      (right.HiddenState × ((left.HiddenState × H) × Path))) :
      (serviceOutputRight join result).selectHistory (fun record => read record.2.1) selected =
        serviceOutputRight join
          (result.selectHistory (fun record => read record.2.1.2) selected) := by
    dsimp only [serviceOutputRight, State.selectHistory]
    rw [ExecutionState.mapClassical_selectClassical]
    rfl
  change (serviceOutputRight join (body (serviceInputRight join state)).val).selectHistory
    (fun record => read record.2.1) selected = _
  rw [output, natural (serviceInputRight join state)
    (fun record : left.HiddenState × H => read record.2) selected, input]
  rfl

attribute [local irreducible] embedPreserving serviceLeftPreserving serviceRightPreserving

/-- Disjoint children retain both services, all physical storage and each original fiber. -/
lemma parallelPreserving_selectHistory {leftCtx rightCtx : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx)
    {LeftPath RightPath : Type} [Fintype LeftPath] [Fintype RightPath]
    (first : Preserving left.HiddenState leftCtx leftCtx
      (Register.prod rightCtx.register Reference) LeftPath)
    (second : Preserving right.HiddenState rightCtx rightCtx
      (Register.prod leftCtx.register Reference) RightPath)
    (firstNatural : ∀ {H D : Type} [Fintype H] [DecidableEq D]
      (state : State leftCtx (Register.prod rightCtx.register Reference) (left.HiddenState × H))
      (read : H → D) (selected : D),
      (first state).val.selectHistory (fun record => read record.2.1) selected =
        (first (state.selectHistory (fun record => read record.2) selected)).val)
    (secondNatural : ∀ {H D : Type} [Fintype H] [DecidableEq D]
      (state : State rightCtx (Register.prod leftCtx.register Reference) (right.HiddenState × H))
      (read : H → D) (selected : D),
      (second state).val.selectHistory (fun record => read record.2.1) selected =
        (second (state.selectHistory (fun record => read record.2) selected)).val)
    {H D : Type} [Fintype H] [DecidableEq D]
    (state : State (leftCtx.disjointUnion rightCtx separate) Reference (parent.HiddenState × H))
    (read : H → D) (selected : D) :
    (parallelPreserving join separate first second state).val.selectHistory
        (fun record => read record.2.1) selected =
      (parallelPreserving join separate first second
        (state.selectHistory (fun record => read record.2) selected)).val := by
  let leftRun : Preserving parent.HiddenState
      (leftCtx.disjointUnion rightCtx separate) (leftCtx.disjointUnion rightCtx separate)
      Reference LeftPath := embedServiceLeftPreserving join
    (ContextEmbedding.alongUnion leftCtx rightCtx separate) first
  let rightRun : Preserving parent.HiddenState
      (leftCtx.disjointUnion rightCtx separate) (leftCtx.disjointUnion rightCtx separate)
      Reference RightPath := embedServiceRightPreserving join
    (ContextEmbedding.alongUnionRight leftCtx rightCtx separate) second
  have leftNatural
      (original : State (leftCtx.disjointUnion rightCtx separate) Reference
        (parent.HiddenState × H)) :
      (leftRun original).val.selectHistory (fun record => read record.2.1) selected =
        (leftRun (original.selectHistory (fun record => read record.2) selected)).val :=
    serviceLeftPreserving_selectHistory join
      (embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate) Reference @first)
      (fun {_ _} _ _ supplied project outcome =>
        embedPreserving_selectHistory (Hidden := left.HiddenState) (Path := LeftPath)
          (ContextEmbedding.alongUnion leftCtx rightCtx separate) Reference
          @first @firstNatural supplied project outcome)
      original read selected
  have rightNatural
      (original : State (leftCtx.disjointUnion rightCtx separate) Reference
        (parent.HiddenState × (H × LeftPath))) :
      (rightRun original).val.selectHistory (fun record => read record.2.1.1) selected =
        (rightRun (original.selectHistory (fun record => read record.2.1) selected)).val :=
    serviceRightPreserving_selectHistory join
      (embedPreserving
        (ContextEmbedding.alongUnionRight leftCtx rightCtx separate) Reference @second)
      (fun {_ _} _ _ supplied project outcome =>
        embedPreserving_selectHistory (Hidden := right.HiddenState) (Path := RightPath)
          (ContextEmbedding.alongUnionRight leftCtx rightCtx separate) Reference
          @second @secondNatural supplied project outcome)
      original (fun record : H × LeftPath => read record.1) selected
  have normal
      (original : State (leftCtx.disjointUnion rightCtx separate) Reference
        (parent.HiddenState × H)) :
      (parallelPreserving join separate first second original).val =
        (rightRun (leftRun original).val).val.mapHistory
          (fun record : parent.HiddenState × ((H × LeftPath) × RightPath) =>
            (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) := by
    dsimp only [parallelPreserving, embedServiceLeftPreserving,
      embedServiceRightPreserving, leftRun, rightRun, State.mapHistory]
    exact State.mapClassical_decision
      (C := Store (leftCtx.disjointUnion rightCtx separate) ×
        (parent.HiddenState × ((H × LeftPath) × RightPath)))
      (D := Store (leftCtx.disjointUnion rightCtx separate) ×
        (parent.HiddenState × (H × (LeftPath × RightPath))))
      (R := Register.prod (leftCtx.disjointUnion rightCtx separate).register Reference) _ _
      (rightRun (leftRun original).val).val
      (fun record : Store (leftCtx.disjointUnion rightCtx separate) ×
          (parent.HiddenState × ((H × LeftPath) × RightPath)) =>
        (record.1, (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2)))))
  rw [normal state, normal (state.selectHistory (fun record => read record.2) selected)]
  change ((rightRun (leftRun state).val).val.mapHistory
    (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))).selectHistory
      (fun record => read record.2.1) selected =
    (rightRun (leftRun
      (state.selectHistory (fun record => read record.2) selected)).val).val.mapHistory
        (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))
  rw [State.selectHistory_mapHistory]
  change ((rightRun (leftRun state).val).val.selectHistory
    (fun record => read record.2.1.1) selected).mapHistory _ = _
  exact congrArg
    (fun output : State (leftCtx.disjointUnion rightCtx separate) Reference
        (parent.HiddenState × ((H × LeftPath) × RightPath)) =>
      output.mapHistory
        (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))))
    ((rightNatural (leftRun state).val).trans
      (congrArg
        (fun original : State (leftCtx.disjointUnion rightCtx separate) Reference
            (parent.HiddenState × (H × LeftPath)) => (rightRun original).val)
        (leftNatural state)))

end

end QuantumAlg.Execution
