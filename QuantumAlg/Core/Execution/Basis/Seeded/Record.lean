/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded.Classical
import all QuantumAlg.Core.Execution.Retained.Record
import all QuantumAlg.Core.Base.State.Density.BasisSupport

/-!
# Actual deterministic retained records preserve complete basis-seeded blocks

The actual record may read persistent service state when writing the caller's
store. Positivity first transfers the seed support from each store marginal
to every complete service/history block. Grouping those blocks by the actual
record then preserves the same support in every final store, including stores
of zero mass, without assuming independence from the external reference.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

open scoped BigOperators ComplexOrder

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma block_diagonal_zero {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : Holds seed state) (entry : Store ctx × History)
    (basis : ctx.register.Index) (outside : basis ≠ seed) (reference : Reference.Index) :
    (state.block entry).matrix (basis, reference) (basis, reference) = 0 := by
  have total := congrArg
    (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      matrix (basis, reference) (basis, reference)) (store_matrix state entry.1)
  have absent := (seeded entry.1 basis basis reference reference).trans
    (if_neg (fun same => outside same.1))
  have totalZero : (∑ original : Store ctx × History, if original.1 = entry.1 then
      (state.block original).matrix (basis, reference) (basis, reference) else 0) = 0 := by
    simpa only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply,
      Matrix.ite_apply, Matrix.zero_apply] using total.trans absent
  have nonnegative (original : Store ctx × History) : 0 ≤
      if original.1 = entry.1 then
        (state.block original).matrix (basis, reference) (basis, reference) else 0 := by
    split_ifs
    · exact (state.block original).positive.diag_nonneg
    · exact le_rfl
  have bound := Finset.single_le_sum (fun original _ => nonnegative original)
    (Finset.mem_univ entry)
  simp only at bound
  exact le_antisymm (bound.trans_eq totalZero) (state.block entry).positive.diag_nonneg

private lemma block_entry_zero {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {History : Type} [Fintype History]
    (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : Holds seed state) (entry : Store ctx × History)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index)
    (outside : ¬ (left = seed ∧ right = seed)) :
    (state.block entry).matrix (left, leftRef) (right, rightRef) = 0 := by
  by_cases leftSeed : left = seed
  · exact DensityOperator.column_zero_of_diagonal_zero (state.block entry) (right, rightRef)
      (block_diagonal_zero seed state seeded entry right
        (fun rightSeed => outside ⟨leftSeed, rightSeed⟩) rightRef) (left, leftRef)
  · exact DensityOperator.row_zero_of_diagonal_zero (state.block entry) (left, leftRef)
      (block_diagonal_zero seed state seeded entry left leftSeed leftRef) (right, rightRef)

/-- A proved actual retained record preserves the seed in every complete store-reference block. -/
lemma retainedRecord {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {key : StorageKey} {shape : CShape} {fresh : key ∉ ctx.keys}
    (code : Circuit model ctx (ctx.addRetained key shape fresh))
    (environment : model.Environment)
    (step : Store ctx × model.HiddenState →
      (Store (ctx.addRetained key shape fresh) × model.HiddenState) × code.Path)
    (record : Circuit.RetainedRecord code environment step) (seed : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) (seeded : Holds seed state) :
    Holds (ctx := ctx.addRetained key shape fresh) seed
      (code.execute environment Reference state) := by
  let output := code.execute environment Reference state
  change Holds (ctx := ctx.addRetained key shape fresh) seed output
  intro finalStore left right leftRef rightRef
  by_cases supported : left = seed ∧ right = seed
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    let update := fun entry : Store ctx × (model.HiddenState × History) =>
      let result := step (entry.1, entry.2.1)
      (result.1.1, (result.1.2, (entry.2.2, result.2)))
    have executedState : output = state.mapClassical update :=
      (record Reference state).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
    have executed := congrArg
      (fun result : State (ctx.addRetained key shape fresh) Reference
        (model.HiddenState × (History × code.Path)) =>
        ((result.mapClassical (fun entry => entry.1)).block finalStore).matrix) executedState
    have grouped := congrArg
      (fun result : ExecutionState (Store (ctx.addRetained key shape fresh))
        (Register.prod ctx.register Reference) => (result.block finalStore).matrix)
      (ExecutionState.executionState_mapClassical_comp state update (fun entry => entry.1))
    have actual := (store_matrix output finalStore).symm.trans (executed.trans grouped)
    have entries := congrArg
      (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
        matrix (left, leftRef) (right, rightRef)) actual
    refine entries.trans ?_
    have absent (entry : Store ctx × (model.HiddenState × History)) :
        (state.block entry).matrix (left, leftRef) (right, rightRef) = 0 :=
      block_entry_zero seed state seeded entry left right leftRef rightRef supported
    simp only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply,
      Matrix.ite_apply, Matrix.zero_apply, absent, ite_self, Finset.sum_const_zero]

end

end QuantumAlg.Execution.BasisSeeded
