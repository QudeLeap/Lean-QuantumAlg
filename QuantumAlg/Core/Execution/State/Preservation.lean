/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Random
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Accounting.Context
import Mathlib.Algebra.Module.BigOperators

/-!
# Classical execution preserves the full quantum and reference marginal

Classical instructions may overwrite storage or merge histories. Summing all
resulting classical blocks nevertheless preserves the complete quantum density
operator, including its coherences with an arbitrary external reference.
Independent uniform choices preserve that same matrix when their outcomes are
summed. These equalities concern the mixed-state representation
[dW19, qcnotes.tex:5381], and impose no injectivity condition on classical updates.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Summing independent uniform classical choices preserves the entire quantum
matrix, rather than only its trace or its computational-basis probabilities. -/
lemma uniformChoice_quantumMarginal {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (count : ℕ+) :
    (uniformChoice state count).quantumMarginal = state.quantumMarginal := by
  have coefficient : (∑ _outcome : Fin count, (count : ℝ)⁻¹) = (1 : ℝ) := by
    have positive : (0 : ℝ) < count := by exact_mod_cast count.pos
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt positive)
  apply DensityOperator.ext
  change (∑ result : C × Fin count, ((uniformChoice state count).block result).matrix) =
    ∑ value : C, (state.block value).matrix
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro value _
  simp only [uniformChoice_block_matrix]
  rw [← Finset.sum_smul, coefficient, one_smul]

namespace State

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H K : Type} [Fintype H] [Fintype K]

/-- Reorganizing or merging histories preserves the complete quantum-reference state. -/
lemma mapHistory_quantumMarginal (state : State ctx Reference H) (f : H → K) :
    (state.mapHistory f).quantumMarginal = state.quantumMarginal :=
  ExecutionState.mapClassical_quantumMarginal state _

/-- Recording a deterministic path leaves the entire quantum-reference marginal unchanged. -/
lemma skip_quantumMarginal (state : State ctx Reference H) :
    (skip state).quantumMarginal = state.quantumMarginal :=
  mapHistory_quantumMarginal state _

/-- Actual classical reads and writes preserve the joint quantum-reference marginal,
including when several previous storage values produce the same written value. -/
lemma classicalStep_quantumMarginal (state : State ctx Reference H)
    {input output : CShape} (op : ClassicalOp input output ctx ctx) :
    (classicalStep state op).quantumMarginal = state.quantumMarginal :=
  ExecutionState.mapClassical_quantumMarginal state _

/-- Retaining a new classical cell changes no part of the quantum-reference marginal. -/
lemma retain_quantumMarginal (state : State ctx Reference H)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (retain state key shape fresh).quantumMarginal = state.quantumMarginal :=
  ExecutionState.mapClassical_quantumMarginal state _

/-- Entering classical workspace preserves the entire quantum-reference state. -/
lemma pushWorkspace_quantumMarginal (state : State ctx Reference H)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (pushWorkspace state key shape fresh).quantumMarginal = state.quantumMarginal :=
  ExecutionState.mapClassical_quantumMarginal state _

/-- Exiting classical workspace sums all its possible stored values while preserving
the complete quantum-reference marginal, without assuming the cell was unmodified. -/
lemma popWorkspace_quantumMarginal (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) (state : State (ctx.addWorkspace key shape fresh) Reference H) :
    (popWorkspace key shape fresh state).quantumMarginal = state.quantumMarginal :=
  ExecutionState.mapClassical_quantumMarginal state _

/-- Generating, storing, and recording uniform bits preserves the joint quantum-reference state. -/
lemma randomBits_quantumMarginal (state : State ctx Reference H) (width : Nat)
    (output : CWriteRef ctx (.bits width)) :
    (randomBits state width output).quantumMarginal = state.quantumMarginal := by
  exact (ExecutionState.mapClassical_quantumMarginal _ _).trans
    (uniformChoice_quantumMarginal state ⟨2 ^ width, Nat.two_pow_pos width⟩)

end State

end

end QuantumAlg.Execution
