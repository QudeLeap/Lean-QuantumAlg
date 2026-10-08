/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Execution

/-!
# Execution of allocations with two resident frames

The recursive allocation is proved independently of any algorithm instance.
Context equalities associate resident entries without replacing instructions,
restricting the input state or discarding service, reference or history blocks.
-/

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

open ContextUnion

variable {model : ExecutionModel}

attribute [local irreducible] storeFintype

private theorem inputCast_heq {pre next post : RuntimeCtx model.kind}
    (same : pre = next) (code : Circuit model next post) :
    HEq (Eq.mpr (congrArg (fun ctx => Circuit model ctx post) same) code) code := by
  cases same
  rfl

private theorem outputCast_heq {pre post next : RuntimeCtx model.kind}
    (same : post = next) (code : Circuit model pre next) :
    HEq (Eq.mpr (congrArg (fun ctx => Circuit model pre ctx) same) code) code := by
  cases same
  rfl

private theorem seq_heq {pre mid post nextPre nextMid nextPost : RuntimeCtx model.kind}
    (first : pre = nextPre) (middle : mid = nextMid) (last : post = nextPost)
    (earlier : Circuit model pre mid) (later : Circuit model mid post)
    (nextEarlier : Circuit model nextPre nextMid) (nextLater : Circuit model nextMid nextPost)
    (sameEarlier : HEq earlier nextEarlier) (sameLater : HEq later nextLater) :
    HEq (earlier.seq later) (nextEarlier.seq nextLater) := by
  cases first
  cases middle
  cases last
  cases sameEarlier
  cases sameLater
  rfl

private theorem retain_heq {ctx next : RuntimeCtx model.kind} (same : ctx = next)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) (nextFresh : key ∉ next.keys) :
    HEq (Circuit.retain (model := model) ctx key shape fresh)
      (Circuit.retain (model := model) next key shape nextFresh) := by
  cases same
  rfl

private theorem id_heq {ctx next : RuntimeCtx model.kind} (same : ctx = next) :
    HEq (Circuit.id (model := model) ctx) (Circuit.id (model := model) next) := by
  cases same
  rfl

private theorem context_eq_model {kind : ProblemKind} (first second : RuntimeCtx kind)
    (entries : first.entries = second.entries) : first = second := by
  cases first
  cases second
  cases entries
  rfl

private theorem union_assoc_model (left right framed : RuntimeCtx model.kind)
    (original : RuntimeCtx.StorageDisjoint left right)
    (outside : RuntimeCtx.StorageDisjoint (left.disjointUnion right original) framed)
    (rightOutside : RuntimeCtx.StorageDisjoint right framed)
    (combined : RuntimeCtx.StorageDisjoint left (right.disjointUnion framed rightOutside)) :
    (left.disjointUnion right original).disjointUnion framed outside =
      left.disjointUnion (right.disjointUnion framed rightOutside) combined :=
  context_eq_model _ _ (List.append_assoc _ _ _)

private theorem pairWithUnit_eq {α : Type} (value : α × Unit) :
    (value.1, ()) = value := Prod.ext rfl (Subsingleton.elim _ _)

private theorem retainedRecordPath_eq {S K V H P Q : Type}
    (paths : P × Unit → Q × Unit)
    (value : S × ((K × ((V × H) × P)) × Unit)) :
    (value.1, (value.2.1.1, (value.2.1.2.1.1,
      (value.2.1.2.1.2, ((paths (value.2.1.2.2, ())).1, value.2.2))))) =
    (value.1, (value.2.1.1, (value.2.1.2.1.1,
      (value.2.1.2.1.2, paths (value.2.1.2.2, value.2.2))))) := by
  cases value.2.2
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl
    (Prod.ext rfl (pairWithUnit_eq _))))

private theorem recordMap_comp {C D K : Type} [Fintype C] [Fintype D] [Fintype K]
    {R : Register} {middle : DecidableEq D} {last : DecidableEq K}
    (state : ExecutionState C R) (first : C → D) (second : D → K) :
    @ExecutionState.mapClassical D K _ _ R last
        (@ExecutionState.mapClassical C D _ _ R middle state first) second =
      @ExecutionState.mapClassical C K _ _ R (Classical.decEq K) state (second ∘ first) :=
  ExecutionState.executionState_mapClassical_comp_instances state first second

section

attribute [local irreducible] ExecutionState.mapClassical

/-- Reassociate two resident frames around every actual retained-cell allocation.
All models, arbitrary input blocks, external references, hidden state and prior
history are preserved, including zero cells and every original allocation path. -/
theorem allocateFramed_associated_execute
    (ctx resident framed : RuntimeCtx model.kind) (dimension : ℕ+) :
    ∀ (count : Nat)
      (original : RuntimeCtx.StorageDisjoint
        (MeasurementCells.context ctx dimension count) resident)
      (outside : RuntimeCtx.StorageDisjoint
        ((MeasurementCells.context ctx dimension count).disjointUnion resident original) framed)
      (rightOutside : RuntimeCtx.StorageDisjoint resident framed)
      (combined : RuntimeCtx.StorageDisjoint (MeasurementCells.context ctx dimension count)
        (resident.disjointUnion framed rightOutside))
      (initial : RuntimeCtx.StorageDisjoint
        (ctx.disjointUnion resident
          (MeasurementCells.original_disjoint ctx resident dimension count original)) framed)
      (actual : Circuit model
        ((ctx.disjointUnion resident
          (MeasurementCells.original_disjoint ctx resident dimension count original)).disjointUnion
            framed initial)
        (RuntimeCtx.disjointUnion
          ((MeasurementCells.context ctx dimension count).disjointUnion resident original)
          framed outside))
      (_same : HEq actual (MeasurementCells.allocateFramed (model := model) ctx
        (resident.disjointUnion framed rightOutside) dimension count combined))
      (paths : (MeasurementCells.allocateFramed (model := model)
        ctx resident dimension count original).Path →
        actual.Path) (Reference : Register) {History : Type} [Fintype History]
      (state : State
        ((ctx.disjointUnion resident
          (MeasurementCells.original_disjoint ctx resident dimension count original)).disjointUnion
            framed initial) Reference (model.HiddenState × History)),
      splitServiceState
        ((MeasurementCells.context ctx dimension count).disjointUnion resident original)
        framed outside (actual.execute Reference state) =
        ((MeasurementCells.allocateFramed (model := model)
          ctx resident dimension count original).execute
          (Register.prod framed.register Reference)
          (splitServiceState (ctx.disjointUnion resident
            (MeasurementCells.original_disjoint ctx resident dimension count original))
            framed initial state)).mapHistory
              (fun record => (record.1,
                (record.2.1.1, (record.2.1.2, paths record.2.2)))) := by
  intro count
  induction count with
  | zero =>
      intro original outside rightOutside combined initial actual same paths Reference
        History _ state
      have entries := union_assoc_model ctx resident framed original outside rightOutside combined
      have actualId : actual = .id ((ctx.disjointUnion resident original).disjointUnion
          framed outside) :=
        eq_of_heq (same.trans (id_heq (model := model) entries).symm)
      subst actual
      change splitServiceState (ctx.disjointUnion resident original) framed outside
        ((Circuit.id (model := model) _).execute Reference state) =
        ((Circuit.id (model := model) _).execute
          (Register.prod framed.register Reference)
          (splitServiceState (ctx.disjointUnion resident original)
            framed outside state)).mapHistory _
      rw [MeasurementCells.id_as_history, MeasurementCells.id_as_history]
      unfold splitServiceState
      erw [contextUnion_splitState_mapHistory, contextUnion_splitState_skip]
      simp only [State.skip, State.mapHistory_comp, Function.comp_def]
      simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def]
      congr 1
  | succ count ih =>
      intro original outside rightOutside combined initial actual same paths Reference
        History _ state
      let middle := MeasurementCells.context ctx dimension count
      let key := middle.canonicalFreshKey
      let shape : CShape := .finite dimension
      let fresh := middle.canonicalFreshKey_fresh
      let originalPrefix := MeasurementCells.retained_disjoint key shape fresh original
      let originalFresh := MeasurementCells.retained_fresh_union key shape fresh original
      let outsidePrefix := MeasurementCells.retained_disjoint key shape originalFresh outside
      let combinedPrefix := MeasurementCells.retained_disjoint key shape fresh combined
      let expandedPrefix := MeasurementCells.allocateFramed (model := model) ctx
        (resident.disjointUnion framed rightOutside) dimension count combinedPrefix
      have first := union_assoc_model ctx resident framed
        (MeasurementCells.original_disjoint ctx resident dimension count originalPrefix)
        initial rightOutside
        (MeasurementCells.original_disjoint ctx
          (resident.disjointUnion framed rightOutside) dimension count combinedPrefix)
      have mid := union_assoc_model middle resident framed originalPrefix outsidePrefix
        rightOutside combinedPrefix
      have last := union_assoc_model (MeasurementCells.context ctx dimension (count + 1))
        resident framed original outside rightOutside combined
      let earlierCode : Circuit model
          (RuntimeCtx.disjointUnion
            (ctx.disjointUnion resident
              (MeasurementCells.original_disjoint ctx resident dimension count originalPrefix))
            framed initial)
          ((middle.disjointUnion resident originalPrefix).disjointUnion framed outsidePrefix) :=
        Eq.mpr (congrArg (fun pre => Circuit model pre
          ((middle.disjointUnion resident originalPrefix).disjointUnion framed outsidePrefix))
            first)
          (Eq.mpr (congrArg (fun post => Circuit model
            (ctx.disjointUnion (resident.disjointUnion framed rightOutside)
              (MeasurementCells.original_disjoint ctx
                (resident.disjointUnion framed rightOutside) dimension count combinedPrefix)) post)
                  mid) expandedPrefix)
      have samePrefix : HEq earlierCode expandedPrefix :=
        (inputCast_heq (model := model) first _).trans
          (outputCast_heq (model := model) mid expandedPrefix)
      let actualFresh := MeasurementCells.retained_fresh_union key shape originalFresh outside
      let retained := Circuit.retain (model := model)
        ((middle.disjointUnion resident originalPrefix).disjointUnion framed outsidePrefix)
        key shape actualFresh
      have sameRetain := retain_heq (model := model) mid key shape actualFresh
        (MeasurementCells.retained_fresh_union key shape fresh combined)
      have decomposed : actual = earlierCode.seq retained := by
        apply eq_of_heq
        exact same.trans (seq_heq (model := model) first mid last
          earlierCode retained expandedPrefix
          (Circuit.retain (model := model)
            (middle.disjointUnion (resident.disjointUnion framed rightOutside)
            combinedPrefix) key shape
              (MeasurementCells.retained_fresh_union key shape fresh combined))
          samePrefix sameRetain).symm
      subst actual
      let prefixPaths :
          (MeasurementCells.allocateFramed (model := model)
            ctx resident dimension count originalPrefix).Path →
            earlierCode.Path := fun path => (paths (path, ())).1
      have prior := ih originalPrefix outsidePrefix rightOutside combinedPrefix initial
        earlierCode samePrefix prefixPaths Reference state
      change splitServiceState
          ((middle.addRetained key shape fresh).disjointUnion resident original) framed outside
          (((retained.execute Reference (earlierCode.execute Reference state))).mapHistory
            (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))) = _
      have splitMapped := contextUnion_splitServiceState_mapHistory
        ((middle.addRetained key shape fresh).disjointUnion resident original) framed outside
        (retained.execute Reference (earlierCode.execute Reference state))
        (fun history => (history.1.1, (history.1.2, history.2)))
      erw [splitMapped]
      have retainedNatural := MeasurementCells.retain_splitServiceState (model := model)
        (ctx := middle.disjointUnion resident originalPrefix) (frame := framed)
        key shape originalFresh outside (Reference := Reference)
        (earlierCode.execute Reference state)
      erw [retainedNatural]
      rw [prior, State.mapHistory_retain]
      change _ = (((MeasurementCells.allocateFramed (model := model) ctx resident dimension count
        originalPrefix).seq (Circuit.retain (model := model)
          (middle.disjointUnion resident originalPrefix) key shape originalFresh)).execute
            (Register.prod framed.register Reference)
            (splitServiceState (ctx.disjointUnion resident
              (MeasurementCells.original_disjoint ctx resident dimension count originalPrefix))
              framed initial state)).mapHistory _
      rw [Circuit.execute_seq, MeasurementCells.retain_as_history]
      simp only [State.mapHistory,
        recordMap_comp,
        Function.comp_def]
      refine (recordMap_comp _ _ _).trans ?_
      apply ExecutionState.executionState_mapClassical_congr
      funext value
      dsimp only [prefixPaths]
      exact retainedRecordPath_eq paths value


end

end

end QuantumAlg.Execution.MeasurementCells
