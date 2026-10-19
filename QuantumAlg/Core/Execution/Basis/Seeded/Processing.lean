/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# Complete basis seed under deterministic real store processing

Changing the classical store and its history groups complete old density
blocks. Their common physical basis seed survives, including zero-mass
records and arbitrary external-reference correlations. No circuit instruction,
input distribution or preparation is introduced by this observation law.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A deterministic actual store/history map preserves every complete physical seed block. -/
lemma mapStore {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
    {History Later : Type} [Fintype History] [Fintype Later]
    {decision : DecidableEq (Store ctx × Later)} (seed : ctx.register.Index)
    (state : State ctx Reference History) (seeded : Holds seed state)
    (storeMap : Store ctx → Store ctx) (historyMap : Store ctx × History → Later) :
    Holds seed (@ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
      decision state (fun entry => (storeMap entry.1, historyMap entry))) := by
  let output := @ExecutionState.mapClassical _ _ _ _
    (Register.prod ctx.register Reference) decision state
      (fun entry => (storeMap entry.1, historyMap entry))
  change Holds seed output
  intro original left right leftRef rightRef
  by_cases supported : left = seed ∧ right = seed
  · obtain ⟨rfl, rfl⟩ := supported
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg supported).symm
    have entries := mapStore_entry_zero state storeMap historyMap original
      (left, leftRef) (right, rightRef)
      (outside_entry seed state seeded left right leftRef rightRef supported)
    have equation : output =
        @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
          (@instDecidableEqProd (Store ctx) Later (Classical.decEq _) (Classical.decEq _))
          state (fun entry => (storeMap entry.1, historyMap entry)) :=
      congrArg
        (fun instanceChoice : DecidableEq (Store ctx × Later) =>
          @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
            instanceChoice state (fun entry => (storeMap entry.1, historyMap entry)))
        (Subsingleton.elim _ _)
    have grouped := congrArg
      (fun result : State ctx Reference Later =>
        ((result.mapClassical (fun entry => entry.1)).block original).matrix
          (left, leftRef) (right, rightRef)) equation
    exact (congrArg
      (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
        matrix (left, leftRef) (right, rightRef))
      (store_matrix output original)).symm.trans (grouped.trans entries)

end

end QuantumAlg.Execution.BasisSeeded
