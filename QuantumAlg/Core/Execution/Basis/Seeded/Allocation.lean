/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded.Classical
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Actual classical allocation preserves complete basis-seeded blocks

Retaining a real classical cell groups old complete store blocks without
changing their quantum matrix entries. Sequential execution only reassociates
the finite history. These facts preserve the existing seed invariant through
the actual measurement-cell allocator, using its physical wire and basis
correspondence at every step, including the empty allocation.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem mapStore_entry_zero {C D H K : Type}
    [Fintype C] [Fintype D] [Fintype H] [Fintype K] {R : Register}
    (state : ExecutionState (C × H) R) (storeMap : C → D) (historyMap : C × H → K)
    (result : D) (left right : R.Index)
    (vanishes : ∀ original : C,
      ((state.mapClassical (fun entry => entry.1)).block original).matrix left right = 0) :
    (((state.mapClassical (fun entry => (storeMap entry.1, historyMap entry))).mapClassical
      (fun entry => entry.1)).block result).matrix left right = 0 := by
  have entries := congrArg (fun matrix : HilbertOperator R => matrix left right)
    (mapStore_block_matrix state storeMap historyMap result)
  exact entries.trans (by
    simp only [Matrix.sum_apply, Matrix.ite_apply, vanishes, Matrix.zero_apply,
      ite_self, Finset.sum_const_zero])

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {History : Type} [Fintype History]

private theorem outside_entry (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : Holds seed state) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) (outside : ¬ (left = seed ∧ right = seed))
    (original : Store ctx) :
    ((state.mapClassical (fun entry => entry.1)).block original).matrix
      (left, leftRef) (right, rightRef) = 0 :=
  (congrArg
    (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      matrix (left, leftRef) (right, rightRef))
    (store_matrix state original)).trans
      ((seeded original left right leftRef rightRef).trans (if_neg outside))

/-- Changing only the actual finite history keeps every complete store seed block. -/
theorem mapHistory (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : Holds seed state) {Later : Type} [Fintype Later] (update : History → Later) :
    Holds seed (state.mapHistory update) := by
  intro original left right leftRef rightRef
  by_cases supported : left = seed ∧ right = seed
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    have entries := mapStore_entry_zero state id (fun entry => update entry.2) original
      (left, leftRef) (right, rightRef)
      (outside_entry seed state seeded left right leftRef rightRef supported)
    exact (congrArg
      (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
        matrix (left, leftRef) (right, rightRef))
      (store_matrix (state.mapHistory update) original)).symm.trans entries

/-- Erasing only a finite path cannot create physical seed support that was
absent from a complete original store-reference block. -/
theorem of_mapHistory (seed : ctx.register.Index) (state : State ctx Reference History)
    {Later : Type} [Fintype Later] (update : History → Later)
    (seeded : Holds seed (state.mapHistory update)) : Holds seed state := by
  have unchanged (original : Store ctx) :
      ((state.mapHistory update).filterClassical
        (fun entry => entry.1 = original)).quantumMarginal =
      (state.filterClassical
        (fun entry => entry.1 = original)).quantumMarginal := by
    have mapped :
        (state.mapHistory update).mapClassical (fun entry => entry.1) =
          state.mapClassical (fun entry => entry.1) := by
      change (state.mapClassical
        (fun entry => (entry.1, update entry.2))).mapClassical
          (fun entry => entry.1) = _
      calc
        _ = state.mapClassical
            ((fun entry => entry.1) ∘
              (fun entry => (entry.1, update entry.2))) :=
          ExecutionState.executionState_mapClassical_comp_instances state _ _
        _ = _ := ExecutionState.executionState_mapClassical_congr _ rfl
    apply DensityOperator.ext
    exact (store_matrix (state.mapHistory update) original).symm.trans
      ((congrArg (fun result : ExecutionState (Store ctx)
        (Register.prod ctx.register Reference) =>
          (result.block original).matrix) mapped).trans
        (store_matrix state original))
  intro original left right leftRef rightRef
  have result := seeded original left right leftRef rightRef
  rw [unchanged original] at result
  exact result

private theorem retain_raw (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : Holds seed state) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    Holds (ctx := ctx.addRetained key shape fresh) seed
      (state.retain key shape fresh) := by
  let output := state.retain key shape fresh
  change Holds (ctx := ctx.addRetained key shape fresh) seed output
  intro original left right leftRef rightRef
  by_cases supported : left = seed ∧ right = seed
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    have entries := mapStore_entry_zero state
      (fun store => store.pushRetained key shape fresh) (fun entry => (entry.2, ())) original
      (left, leftRef) (right, rightRef)
      (outside_entry seed state seeded left right leftRef rightRef supported)
    have equation : output =
        @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
          (@instDecidableEqProd (Store (ctx.addRetained key shape fresh)) (History × Unit)
            (Classical.decEq _) (Classical.decEq _)) state
          (fun entry => (entry.1.pushRetained key shape fresh, (entry.2, ()))) :=
      congrArg
        (fun decision : DecidableEq (Store (ctx.addRetained key shape fresh) × (History × Unit)) =>
          @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
            decision state (fun entry => (entry.1.pushRetained key shape fresh, (entry.2, ()))))
        (Subsingleton.elim _ _)
    have grouped := congrArg
      (fun result : State (ctx.addRetained key shape fresh) Reference (History × Unit) =>
        ((result.mapClassical (fun entry => entry.1)).block original).matrix
          (left, leftRef) (right, rightRef)) equation
    exact (congrArg
      (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
        matrix (left, leftRef) (right, rightRef))
      (store_matrix output original)).symm.trans (grouped.trans entries)

/-- A real retained cell preserves the seeded basis and the persistent service state. -/
theorem retain {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (seed : ctx.register.Index) (state : State ctx Reference (model.HiddenState × History))
    (seeded : Holds seed state) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    Holds (ctx := ctx.addRetained key shape fresh) seed
      ((Circuit.retain (model := model) ctx key shape fresh).execute Reference state) := by
  exact mapHistory (ctx := ctx.addRetained key shape fresh) seed (state.retain key shape fresh)
    (retain_raw seed state seeded key shape fresh)
    (fun record => (record.1.1, (record.1.2, record.2)))

/-- The real sequential interpreter has the seed of its actually executed second body. -/
theorem seq {model : ExecutionModel} {ctx middle post : RuntimeCtx model.kind}
    (first : Circuit model ctx middle) (second : Circuit model middle post)
    (seed : post.register.Index)
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : Holds seed (second.execute Reference (first.execute Reference state))) :
    Holds seed ((Circuit.seq first second).execute Reference state) := by
  intro original left right leftRef rightRef
  have actual := Circuit.seq_store_marginal first second state original
  have entry := congrArg
    (fun density : DensityOperator (Register.prod post.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) actual
  have seedEntry := congrArg
    (fun density : DensityOperator (Register.prod post.register Reference) =>
      density.matrix (seed, leftRef) (seed, rightRef)) actual
  exact entry.trans ((seeded original left right leftRef rightRef).trans
    (congrArg (fun coefficient : ℂ =>
      if left = seed ∧ right = seed then coefficient else 0) seedEntry.symm))

end

end QuantumAlg.Execution.BasisSeeded

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

/-- Actual retained measurement cells preserve the seed in the existing physical basis map. -/
theorem allocate_seeded {model : ExecutionModel} (ctx : RuntimeCtx model.kind)
    (dimension : ℕ+) (count : Nat) (seed : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds (ctx := context ctx dimension count) (basisEquiv ctx dimension count seed)
      ((allocate (model := model) ctx dimension count).execute Reference state) := by
  induction count with
  | zero =>
      exact BasisSeeded.mapHistory seed
        (state.skip) (BasisSeeded.mapHistory seed state seeded (fun history => (history, ())))
        (fun record => (record.1.1, (record.1.2, record.2)))
  | succ count induction =>
      exact BasisSeeded.seq (allocate (model := model) ctx dimension count)
        (.retain (context ctx dimension count) (context ctx dimension count).canonicalFreshKey
          (.finite dimension) (context ctx dimension count).canonicalFreshKey_fresh)
        (basisEquiv ctx dimension (count + 1) seed) state
        (BasisSeeded.retain (basisEquiv ctx dimension count seed)
          ((allocate (model := model) ctx dimension count).execute Reference state) induction
          (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh)

end

end QuantumAlg.Execution.MeasurementCells
