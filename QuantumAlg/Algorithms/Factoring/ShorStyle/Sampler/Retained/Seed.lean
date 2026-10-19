/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Execution
import all QuantumAlg.Core.Execution.Basis.Seeded.Classical

/-!
# Actual retained sampling preserves any complete store-reference basis seed

The existing sampler execution is its real uniform draw followed by its
actual retained-store update and actual path. Grouping that execution by
complete final store sums old store blocks with the same uniform coefficient.
Every such block therefore keeps the supplied basis seed, including arbitrary
correlations among the original classical storage and external reference.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual retained source sampling preserves the seed on every complete store-reference block. -/
lemma samplerRetained_seeded {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {N : Nat} (input : Input N)
    (seed : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds (ctx := context ctx N) seed
      ((circuit (model := model) ctx N).execute environment Reference state) := by
  let sampled := (circuit (model := model) ctx N).execute environment Reference state
  change BasisSeeded.Holds (ctx := context ctx N) seed sampled
  intro finalStore left right leftRef rightRef
  by_cases supported : left = seed ∧ right = seed
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    let count : ℕ+ := ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩
    let histories := fun entry : (Store ctx × (model.HiddenState × History)) × Fin count =>
      (entry.1.2.1, (entry.1.2.2, resultPath (model := model) ctx N entry.1.1 entry.2))
    have executedState : sampled =
        @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
          (@instDecidableEqProd (Store (context ctx N))
            (model.HiddenState × (History × (circuit (model := model) ctx N).Path))
            (Classical.decEq _) (Classical.decEq _))
          (uniformChoice state count)
          (fun entry =>
            (resultStore input entry.1.1 entry.2, histories entry)) := by
      refine (samplerRetained_execute (environment := environment)
        ctx input Reference state).trans ?_
      exact mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
    have executed := congrArg
      (fun output : State (context ctx N) Reference
          (model.HiddenState × (History × (circuit (model := model) ctx N).Path)) =>
        ((output.mapClassical (fun entry => entry.1)).block finalStore).matrix)
      executedState
    have grouped := BasisSeeded.sampledMap_store_matrix state count
      (resultStore input) histories finalStore
    have actual := (BasisSeeded.store_matrix sampled finalStore).symm.trans
      (executed.trans grouped)
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
        (BasisSeeded.store_matrix state original)).trans
        ((seeded original left right leftRef rightRef).trans (if_neg supported))
    simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.smul_apply, Matrix.zero_apply, absent,
      smul_zero, ite_self, Finset.sum_const_zero]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
