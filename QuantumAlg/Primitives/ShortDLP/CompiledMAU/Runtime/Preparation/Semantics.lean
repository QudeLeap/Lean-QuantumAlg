/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Preparation.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# The first actual bank preparation establishes the complete seed invariant

The preparation interpreter's tensor entries vanish outside the declared
basis label in every old classical block. Its actual store extension and
path update only sum such blocks. The resulting complete store-reference
blocks therefore establish the same seed invariant that reset/reload later
reestablishes, with arbitrary old classical/reference correlations.

No normalization, particular classical value or independent reference is
assumed. The empty incoming quantum layout belongs to the internal first
allocation boundary; later rounds reuse the resulting owned bank.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeBank

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private theorem prepared_support {ctx : RuntimeCtx .quantum} {Reference : Register}
    {C : Type} [Fintype C] {systemCount : Nat}
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) (empty : ctx.systemCount = 0)
    (value : C) (row column : (ctx.addOwnedLayout key layout fresh disjoint).register.Index)
    (leftRef rightRef : Reference.Index)
    (outside : ¬ (row =
      preparedEmptyBasisEquiv ctx key layout fresh disjoint empty preparation.value ∧
      column = preparedEmptyBasisEquiv ctx key layout fresh disjoint empty preparation.value)) :
    ((prepareContext state key layout fresh disjoint preparation.normalized).block value).matrix
      (row, leftRef) (column, rightRef) = 0 := by
  let assembly := preparedEmptyBasisEquiv ctx key layout fresh disjoint empty
  obtain ⟨sourceRow, rfl⟩ := assembly.surjective row
  obtain ⟨sourceColumn, rfl⟩ := assembly.surjective column
  have entry := prepareContext_joined_entry state key layout fresh disjoint
    preparation.normalized value sourceRow sourceColumn
    (emptyContextBasis ctx empty, leftRef) (emptyContextBasis ctx empty, rightRef)
  change DensityOperator.matrix
    ((prepareContext state key layout fresh disjoint preparation.normalized).block value)
    (assembly sourceRow, leftRef) (assembly sourceColumn, rightRef) =
      (preparation.normalized sourceRow * star (preparation.normalized sourceColumn)) *
        (state.block value).matrix (emptyContextBasis ctx empty, leftRef)
          (emptyContextBasis ctx empty, rightRef) at entry
  by_cases hrow : sourceRow = preparation.value
  · by_cases hcolumn : sourceColumn = preparation.value
    · exact False.elim (outside ⟨congrArg assembly hrow, congrArg assembly hcolumn⟩)
    · exact entry.trans (by simp [BasisPreparation.normalized, hcolumn])
  · exact entry.trans (by simp [BasisPreparation.normalized, hrow])

private theorem mapped_support {C D : Type} [Fintype C] [Fintype D]
    {R Reference : Register} (state : ExecutionState C (Register.prod R Reference))
    (update : C → D) (seed : R.Index)
    (supported : ∀ (value : C) (row column : R.Index) (leftRef rightRef : Reference.Index),
      ¬ (row = seed ∧ column = seed) →
        (state.block value).matrix (row, leftRef) (column, rightRef) = 0)
    (value : D) (row column : R.Index) (leftRef rightRef : Reference.Index)
    (outside : ¬ (row = seed ∧ column = seed)) :
    ((state.mapClassical update).block value).matrix (row, leftRef) (column, rightRef) = 0 := by
  rw [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro original _
  split
  · exact supported original row column leftRef rightRef outside
  · rfl

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])
  (m ell width : Nat)

/-- The actual allocation establishes the seed on every complete store-reference block. -/
theorem shortDLP_runtimePrepare_seedBlocks (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    RuntimeRound.HasSeedBlocks m ell width
      (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width) N
      ((prepare ctx noQuantum m ell width N).execute Reference state) := by
  let layout := runtimeLayout m ell width
  let disjoint := allocationDisjoint ctx noQuantum m ell width
  let preparation := seedPreparation m ell width N
  let bank := context ctx noQuantum m ell width
  let seed := (RuntimePlacement.basisEquiv m ell width
    (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width)).symm
      (CompiledMAU.reloadLabel m ell width N)
  let prepared := prepareContext state ctx.canonicalFreshKey layout ctx.canonicalFreshKey_fresh
    disjoint preparation.normalized
  let update := fun entry : Store ctx × History =>
    (entry.1.pushOwnedLayout ctx.canonicalFreshKey layout ctx.canonicalFreshKey_fresh disjoint,
      (entry.2, ()))
  have seedLabel :
      preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey layout ctx.canonicalFreshKey_fresh
        disjoint (input_systemCount ctx noQuantum) preparation.value = seed :=
    (shortDLP_runtimePrepared_basis ctx noQuantum m ell width preparation.value).trans
      (congrArg (RuntimePlacement.basisEquiv m ell width
        (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width)).symm
        ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.apply_symm_apply
          (CompiledMAU.reloadLabel m ell width N)))
  have support (value : Store ctx × History) (row column : bank.register.Index)
      (leftRef rightRef : Reference.Index) (outside : ¬ (row = seed ∧ column = seed)) :
      (prepared.block value).matrix (row, leftRef) (column, rightRef) = 0 :=
    prepared_support state ctx.canonicalFreshKey layout ctx.canonicalFreshKey_fresh
      disjoint preparation (input_systemCount ctx noQuantum) value row column leftRef rightRef
      (fun same => outside ⟨same.1.trans seedLabel, same.2.trans seedLabel⟩)
  have mapped := mapped_support prepared update seed support
  let output : State bank Reference (History × Unit) := prepared.mapClassical update
  change RuntimeRound.HasSeedBlocks m ell width
    (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width) N output
  intro original row column leftRef rightRef
  by_cases same : row = seed ∧ column = seed
  · obtain ⟨rfl, rfl⟩ := same
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg same).symm
    change (∑ entry : Store bank × (History × Unit),
      ((output.filterClassical (fun entry => entry.1 = original)).block entry).matrix)
        (row, leftRef) (column, rightRef) = 0
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro entry _
    simp only [ExecutionState.filterClassical_block]
    split
    · change ((prepared.mapClassical update).block entry).matrix
        (row, leftRef) (column, rightRef) = 0
      have decisionEntry := congrArg
        (fun decision : DecidableEq (Store bank × (History × Unit)) =>
          ((@ExecutionState.mapClassical (Store ctx × History)
            (Store bank × (History × Unit)) _ _ (Register.prod bank.register Reference)
            decision prepared update).block entry).matrix
              (row, leftRef) (column, rightRef))
        (Subsingleton.elim
          (inferInstance : DecidableEq (Store bank × (History × Unit)))
          (Classical.decEq (Store bank × (History × Unit))))
      exact decisionEntry.trans (mapped entry row column leftRef rightRef same)
    · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeBank
