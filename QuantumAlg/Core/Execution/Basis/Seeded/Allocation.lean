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

/-- A real retained cell leaves the same physical quantum basis seeded in every final store. -/
theorem retain (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : Holds seed state) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    Holds (ctx := ctx.addRetained key shape fresh) seed
      ((Circuit.retain ctx key shape fresh).execute Reference state) := by
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

/-- The real sequential interpreter has the seed of its actually executed second body. -/
theorem seq {middle post : RuntimeCtx kind} (first : Circuit ctx middle)
    (second : Circuit middle post) (seed : post.register.Index)
    (state : State ctx Reference History)
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
theorem allocate_seeded {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) (seed : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds (ctx := context ctx dimension count) (basisEquiv ctx dimension count seed)
      ((allocate ctx dimension count).execute Reference state) := by
  induction count with
  | zero =>
      exact BasisSeeded.mapHistory seed state seeded (fun history => (history, ()))
  | succ count induction =>
      exact BasisSeeded.seq (allocate ctx dimension count)
        (.retain (context ctx dimension count) (context ctx dimension count).canonicalFreshKey
          (.finite dimension) (context ctx dimension count).canonicalFreshKey_fresh)
        (basisEquiv ctx dimension (count + 1) seed) state
        (BasisSeeded.retain (basisEquiv ctx dimension count seed)
          ((allocate ctx dimension count).execute Reference state) induction
          (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh)

end

end QuantumAlg.Execution.MeasurementCells
