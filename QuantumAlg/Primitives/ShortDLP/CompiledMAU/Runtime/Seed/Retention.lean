/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Results

/-!
# Retaining real round results preserves the actual seed blocks

A retained result cell changes only classical storage. Its actual push keeps
the whole previous store injectively, and history reassociation keeps every
complete store-reference block. These facts transport the internal seed
invariant through the actual constructors used between repeated rounds.

No new state transformation is introduced. In particular, all earlier
results and the actual sampled parameter remain in the retained store.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private theorem mapped_store_marginal {C D H K : Type}
    [Fintype C] [Fintype D] [Fintype H] [Fintype K] {R : Register}
    (state : ExecutionState (C × H) R) (storeMap : C → D) (historyMap : C × H → K)
    (result : D) :
    ((state.mapClassical (fun entry => (storeMap entry.1, historyMap entry))).filterClassical
      (fun entry => entry.1 = result)).quantumMarginal =
      (state.filterClassical (fun entry => storeMap entry.1 = result)).quantumMarginal :=
  (congrArg ExecutionState.quantumMarginal
    (ZReset.filter_map state (fun entry => (storeMap entry.1, historyMap entry))
      (fun entry => entry.1 = result))).trans
    (ExecutionState.mapClassical_quantumMarginal _ _)

private theorem retained_store_injective {ctx : RuntimeCtx .quantum}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    Function.Injective (fun store : Store ctx => store.pushRetained key shape fresh) := by
  intro left right same
  have cells := congrArg
    (fun store : Store (ctx.addRetained key shape fresh) => store.cells.2) same
  cases left
  cases right
  cases cells
  rfl

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Reorganizing actual histories preserves the internal invariant on every complete store. -/
theorem shortDLP_runtimeSeedBlocks_mapHistory (N : Nat)
    {Reference : Register} {History Later : Type} [Fintype History] [Fintype Later]
    (state : State ctx Reference History) (seeded : HasSeedBlocks m ell width sameWires N state)
    (update : History → Later) :
    HasSeedBlocks m ell width sameWires N (state.mapHistory update) := by
  let seed := (RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)
  intro original left right leftRef rightRef
  have marginal := (congrArg ExecutionState.quantumMarginal
    (ZReset.filter_mapHistory state update (fun store => store = original))).trans
    (State.mapHistory_quantumMarginal
      (state.filterClassical (fun entry => entry.1 = original)) update)
  have entry := congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) marginal
  have seedEntry := congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (seed, leftRef) (seed, rightRef)) marginal
  exact entry.trans ((seeded original left right leftRef rightRef).trans
    (congrArg (fun coefficient : ℂ =>
      if left = seed ∧ right = seed then coefficient else 0) seedEntry.symm))

/-- An actual retained classical cell keeps the same source seed and all old store correlations. -/
theorem shortDLP_runtimeSeedBlocks_retain (N : Nat)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (seeded : HasSeedBlocks m ell width sameWires N state) :
    HasSeedBlocks m ell width
      ((RuntimeCtx.quantumWires_addRetained ctx key shape fresh).trans sameWires) N
      ((Circuit.retain ctx key shape fresh).execute Reference state) := by
  let seed := (RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)
  let output := state.retain key shape fresh
  change HasSeedBlocks m ell width
    ((RuntimeCtx.quantumWires_addRetained ctx key shape fresh).trans sameWires) N output
  intro finalStore left right leftRef rightRef
  change (output.filterClassical (fun entry => entry.1 = finalStore)).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) =
    if left = seed ∧ right = seed then
      (output.filterClassical (fun entry => entry.1 = finalStore)).quantumMarginal.matrix
        (seed, leftRef) (seed, rightRef) else 0
  by_cases same : left = seed ∧ right = seed
  · obtain ⟨rfl, rfl⟩ := same
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg same).symm
    have marginal := mapped_store_marginal state
      (fun store => store.pushRetained key shape fresh) (fun entry => (entry.2, ())) finalStore
    have outputEquation : output =
        state.mapClassical (fun entry =>
          (entry.1.pushRetained key shape fresh, (entry.2, ()))) := by
      rfl
    have filteredOutput := congrArg
      (fun result : State (ctx.addRetained key shape fresh) Reference (History × Unit) =>
        (result.filterClassical (fun entry => entry.1 = finalStore)).quantumMarginal)
      outputEquation
    have decisions := congrArg
      (fun decision : DecidableEq (Store (ctx.addRetained key shape fresh) × (History × Unit)) =>
        ((@ExecutionState.mapClassical (Store ctx × History)
          (Store (ctx.addRetained key shape fresh) × (History × Unit)) _ _
          (Register.prod ctx.register Reference) decision state
          (fun entry => (entry.1.pushRetained key shape fresh, (entry.2, ())))).filterClassical
            (fun entry => entry.1 = finalStore)).quantumMarginal)
      (Subsingleton.elim
        (inferInstance : DecidableEq (Store (ctx.addRetained key shape fresh) × (History × Unit)))
        (@instDecidableEqProd (Store (ctx.addRetained key shape fresh)) (History × Unit)
          (Classical.decEq _) (Classical.decEq _)))
    refine (congrArg
      (fun density : DensityOperator (Register.prod ctx.register Reference) =>
        density.matrix (left, leftRef) (right, rightRef))
      (filteredOutput.trans (decisions.trans marginal))).trans ?_
    by_cases reachable : ∃ original : Store ctx, original.pushRetained key shape fresh = finalStore
    · obtain ⟨original, rfl⟩ := reachable
      have filtered :
          state.filterClassical (fun entry => entry.1.pushRetained key shape fresh =
            original.pushRetained key shape fresh) =
          state.filterClassical (fun entry => entry.1 = original) := by
        apply ExecutionState.ext
        intro entry
        simp only [ExecutionState.filterClassical_block,
          (retained_store_injective key shape fresh).eq_iff]
      have entry := congrArg
        (fun part : State ctx Reference History =>
          part.quantumMarginal.matrix (left, leftRef) (right, rightRef)) filtered
      exact entry.trans ((seeded original left right leftRef rightRef).trans (if_neg same))
    · change (∑ entry : Store ctx × History,
        ((state.filterClassical (fun entry => entry.1.pushRetained key shape fresh =
          finalStore)).block entry).matrix) (left, leftRef) (right, rightRef) = 0
      rw [Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro entry _
      have absent : entry.1.pushRetained key shape fresh ≠ finalStore :=
        fun equal => reachable ⟨entry.1, equal⟩
      simp only [ExecutionState.filterClassical_block, absent, if_false,
        DensityOperator.zero_matrix, Matrix.zero_apply]

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
