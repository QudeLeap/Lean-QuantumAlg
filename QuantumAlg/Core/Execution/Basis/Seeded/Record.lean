/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded.Classical
import all QuantumAlg.Core.Execution.Retained.Record

/-!
# Actual deterministic retained records preserve complete basis-seeded blocks

The actual store map groups the original complete store blocks. Its finite
history records remain present, and every off-diagonal reference coordinate
is preserved in that grouping. Support at the same local basis seed therefore
holds separately in every final store, including stores of zero mass.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A proved actual retained record preserves the seed in every complete store-reference block. -/
theorem retainedRecord {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {key : StorageKey} {shape : CShape} {fresh : key ∉ ctx.keys}
    (code : Circuit ctx (ctx.addRetained key shape fresh))
    (step : Store ctx → Store (ctx.addRetained key shape fresh) × code.Path)
    (record : Circuit.RetainedRecord code step) (seed : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (seeded : Holds seed state) :
    Holds (ctx := ctx.addRetained key shape fresh) seed (code.execute Reference state) := by
  let output := code.execute Reference state
  change Holds (ctx := ctx.addRetained key shape fresh) seed output
  intro finalStore left right leftRef rightRef
  by_cases supported : left = seed ∧ right = seed
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    let histories := fun entry : Store ctx × History => (entry.2, (step entry.1).2)
    have executedState : output =
        @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
          (@instDecidableEqProd (Store (ctx.addRetained key shape fresh))
            (History × code.Path) (Classical.decEq _) (Classical.decEq _)) state
          (fun entry => ((step entry.1).1, histories entry)) := by
      refine (record Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
    have executed := congrArg
      (fun result : State (ctx.addRetained key shape fresh) Reference (History × code.Path) =>
        ((result.mapClassical (fun entry => entry.1)).block finalStore).matrix) executedState
    have grouped := mapStore_block_matrix state (fun original => (step original).1)
      histories finalStore
    have actual := (store_matrix output finalStore).symm.trans (executed.trans grouped)
    have entries := congrArg
      (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
        matrix (left, leftRef) (right, rightRef)) actual
    refine entries.trans ?_
    have absent (original : Store ctx) :
        ((state.mapClassical (fun entry => entry.1)).block original).matrix
          (left, leftRef) (right, rightRef) = 0 :=
      (congrArg
        (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
          matrix (left, leftRef) (right, rightRef))
        (store_matrix state original)).trans
          ((seeded original left right leftRef rightRef).trans (if_neg supported))
    simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, absent,
      ite_self, Finset.sum_const_zero]

end

end QuantumAlg.Execution.BasisSeeded
