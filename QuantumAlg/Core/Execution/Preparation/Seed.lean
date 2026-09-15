/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Actual basis preparation establishes every complete store seed block

On an empty incoming quantum layout, the existing preparation interpreter
adjoins its declared basis label. Every old classical-history block keeps
its complete reference operator. The actual store extension and history
record then sum only blocks with that same seed support. No normalization
or reference independence is required.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem prepareContext_empty_outside {ctx : RuntimeCtx .quantum} {Reference : Register}
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

end

end QuantumAlg.Execution

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The real preparation establishes its physical basis seed in every complete stored block. -/
theorem prepare_empty_seeded {ctx : RuntimeCtx .quantum} {systemCount : Nat}
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) (empty : ctx.systemCount = 0)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    BasisSeeded.Holds
      (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty preparation.value)
      ((Circuit.prepare ctx key layout fresh disjoint preparation).execute Reference state) := by
  let seed := preparedEmptyBasisEquiv ctx key layout fresh disjoint empty preparation.value
  let prepared := prepareContext state key layout fresh disjoint preparation.normalized
  let update := fun entry : Store ctx × History =>
    (entry.1.pushOwnedLayout key layout fresh disjoint, (entry.2, ()))
  intro finalStore row column leftRef rightRef
  by_cases same : row = seed ∧ column = seed
  · obtain ⟨rfl, rfl⟩ := same
    exact (if_pos ⟨rfl, rfl⟩).symm
  · refine Eq.trans ?_ (if_neg same).symm
    have executed := congrArg
      (fun output : State (ctx.addOwnedLayout key layout fresh disjoint)
          Reference (History × Unit) =>
        ((output.mapClassical (fun entry => entry.1)).block finalStore).matrix)
      (execute_prepare state key layout fresh disjoint preparation)
    have composed := congrArg
      (fun output : ExecutionState (Store (ctx.addOwnedLayout key layout fresh disjoint))
          (Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference) =>
        (output.block finalStore).matrix)
      (ExecutionState.executionState_mapClassical_comp prepared update (fun entry => entry.1))
    have actual := (BasisSeeded.store_matrix
      ((Circuit.prepare ctx key layout fresh disjoint preparation).execute Reference state)
      finalStore).symm.trans (executed.trans composed)
    refine (congrArg
      (fun matrix : HilbertOperator
          (Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference) =>
        matrix (row, leftRef) (column, rightRef)) actual).trans ?_
    rw [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro original _
    split
    · exact prepareContext_empty_outside state key layout fresh disjoint preparation empty
        original row column leftRef rightRef same
    · rfl

end

end QuantumAlg.Circuit
