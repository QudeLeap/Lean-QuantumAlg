/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store.History
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Reference.Preservation
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Exact actual stored-parameter dispatch fibers

Actual branching selects the original complete Store before executing its
body. The equations retain its original physical matrix and Reference, and
apply to arbitrary old stored values. They describe existing execution and
introduce no independent stochastic callback [dW19, qcnotes.tex:5381-5409].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

lemma measuredSelection_store_matrix {execution : ExecutionModel}
    {environment : execution.Environment}
    {pre post : RuntimeCtx execution.kind} {shape : CShape}
    (input : CInputRef pre shape) (body : shape.Value → Circuit execution pre post)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference (execution.HiddenState × History)) (stored : Store post) :
    (((Circuit.branch input body).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ value : shape.Value,
        (((body value).execute environment Reference
          (state.selectClassical (fun entry => entry.1.read input) value)).filterClassical
            (fun entry => entry.1 = stored)).quantumMarginal.matrix := by
  let selected (value : shape.Value) :=
    (body value).execute environment Reference
      (state.selectClassical (fun entry => entry.1.read input) value)
  let extend (value : shape.Value) :
      execution.HiddenState × (History × (body value).Path) →
        execution.HiddenState × (History × (Circuit.branch input body).Path) :=
    fun history => (history.1, (history.2.1, ⟨value, history.2.2⟩))
  have distribute (result : Store post ×
      (execution.HiddenState × (History × (Circuit.branch input body).Path))) :
      (if result.1 = stored then
        ∑ value : shape.Value,
          (((selected value).mapHistory (extend value)).block result).matrix else 0) =
      ∑ value : shape.Value, if result.1 = stored then
        (((selected value).mapHistory (extend value)).block result).matrix else 0 := by
    by_cases same : result.1 = stored <;>
      simp only [same, if_true, if_false, Finset.sum_const_zero]
  change (∑ result,
    ((((Circuit.branch input body).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).block result).matrix) = _
  simp only [ExecutionState.filterClassical_block, apply_ite DensityOperator.matrix,
    DensityOperator.zero_matrix]
  simp_rw [Circuit.execute_branch_block_matrix]
  change (∑ result, if result.1 = stored then
    ∑ value : shape.Value,
      (((selected value).mapHistory (extend value)).block result).matrix else 0) = _
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  simpa only [ExecutionState.quantumMarginal, ExecutionState.filterClassical_block,
    apply_ite DensityOperator.matrix, DensityOperator.zero_matrix] using
    congrArg DensityOperator.matrix
      (State.mapHistory_store_marginal (selected value) (extend value) stored)

lemma measuredSelection_input_matrix {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape) (value : shape.Value)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx) :
    ((state.selectClassical (fun entry => entry.1.read input) value).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix =
      if original.read input = value then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      else 0 := by
  by_cases reads : original.read input = value
  · rw [if_pos reads]
    have same :
        (state.selectClassical (fun entry => entry.1.read input) value).filterClassical
            (fun entry => entry.1 = original) =
          state.filterClassical (fun entry => entry.1 = original) := by
      apply ExecutionState.ext
      intro entry
      by_cases present : entry.1 = original
      · have selected : entry.1.read input = value := present.symm ▸ reads
        simp only [ExecutionState.filterClassical_block, ExecutionState.selectClassical_block,
          if_pos present, if_pos selected]
      · simp only [ExecutionState.filterClassical_block, if_neg present]
    rw [same]
  · rw [if_neg reads]
    have zero :
        (state.selectClassical (fun entry => entry.1.read input) value).filterClassical
            (fun entry => entry.1 = original) = ExecutionState.zero := by
      apply ExecutionState.ext
      intro entry
      by_cases present : entry.1 = original
      · have absent : entry.1.read input ≠ value := present.symm ▸ reads
        simp only [ExecutionState.filterClassical_block, ExecutionState.selectClassical_block,
          if_pos present, if_neg absent, ExecutionState.zero_block]
      · simp only [ExecutionState.filterClassical_block, if_neg present,
          ExecutionState.zero_block]
    rw [zero]
    simp only [ExecutionState.quantumMarginal, ExecutionState.zero_block,
      DensityOperator.zero_matrix, Finset.sum_const_zero]

/-- Selecting a true stored-value fiber preserves its actual complete physical basis support. -/
lemma measuredSelection_seeded {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (input : CInputRef ctx shape) (value : shape.Value) {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (seed : ctx.register.Index) (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds seed (state.selectClassical (fun entry => entry.1.read input) value) := by
  intro original left right leftRef rightRef
  have entries := measuredSelection_input_matrix input value state original
  by_cases reads : original.read input = value
  · rw [if_pos reads] at entries
    exact (congrArg (fun matrix => matrix (left, leftRef) (right, rightRef)) entries).trans
      ((seeded original left right leftRef rightRef).trans
        (congrArg (fun coefficient : ℂ =>
          if left = seed ∧ right = seed then coefficient else 0)
          (congrArg (fun matrix => matrix (seed, leftRef) (seed, rightRef)) entries).symm))
  · rw [if_neg reads] at entries
    rw [entries]
    simp only [Matrix.zero_apply, ite_self]

/-- The complete selected Store retains the original off-diagonal reference coefficient. -/
lemma measuredSelection_reference_entry {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape) (value : shape.Value)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx)
    (leftRef rightRef : Reference.Index) :
    ((state.selectClassical (fun entry => entry.1.read input) value).filterClassical
      (fun entry => entry.1 = original)).referenceMarginal.matrix leftRef rightRef =
      if original.read input = value then
        (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
          leftRef rightRef
      else 0 := by
  rw [ExecutionState.referenceMarginal_entry, ExecutionState.referenceMarginal_entry]
  simp only [measuredSelection_input_matrix, Matrix.ite_apply, Matrix.zero_apply]
  by_cases reads : original.read input = value <;>
    simp only [reads, if_true, if_false, Finset.sum_const_zero]

/-- The real branch sums its actual selected-input executions, keeping both Reference indices. -/
lemma measuredSelection_referenceFiberSum {execution : ExecutionModel}
    {environment : execution.Environment}
    {pre post : RuntimeCtx execution.kind} {shape : CShape}
    (input : CInputRef pre shape) (body : shape.Value → Circuit execution pre post)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference (execution.HiddenState × History))
    (weight : Store post → post.register.Index → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((Circuit.branch input body).execute environment Reference state)
        (fun entry basis => weight entry.1 basis) leftRef rightRef =
      ∑ value : shape.Value,
        ExecutionState.referenceFiberSum
          ((body value).execute environment Reference
            (state.selectClassical (fun entry => entry.1.read input) value))
          (fun entry basis => weight entry.1 basis) leftRef rightRef := by
  let selected (value : shape.Value) :=
    (body value).execute environment Reference
      (state.selectClassical (fun entry => entry.1.read input) value)
  let term (basis : post.register.Index) (stored : Store post) (value : shape.Value) :=
    weight stored basis *
      ((selected value).filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix
        (basis, leftRef) (basis, rightRef)
  refine (BasisSeeded.fiber_store_blocks
    ((Circuit.branch input body).execute environment Reference state) weight
    leftRef rightRef).trans ?_
  calc
    _ = ∑ basis : post.register.Index, ∑ stored : Store post, ∑ value : shape.Value,
        term basis stored value := by
      apply Finset.sum_congr rfl
      intro basis _
      apply Finset.sum_congr rfl
      intro stored _
      have entries := congrArg
        (fun matrix => matrix (basis, leftRef) (basis, rightRef))
        (measuredSelection_store_matrix (environment := environment) input body state stored)
      rw [entries]
      simp only [Matrix.sum_apply, Finset.mul_sum]
      rfl
    _ = ∑ basis : post.register.Index, ∑ value : shape.Value, ∑ stored : Store post,
        term basis stored value := by
      apply Finset.sum_congr rfl
      intro basis _
      exact Finset.sum_comm
    _ = ∑ value : shape.Value, ∑ basis : post.register.Index, ∑ stored : Store post,
        term basis stored value := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro value _
      exact (BasisSeeded.fiber_store_blocks (selected value) weight leftRef rightRef).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
