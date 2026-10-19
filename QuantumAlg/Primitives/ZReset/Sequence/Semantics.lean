/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Sequence

/-!
# Zero support of actual sequential register reset

The proof uses the existing single-wire measurement and stored correction
semantics [dW19, qcnotes.tex:5405,5409,5420]. A later reset preserves every wire
already reset to zero, even when the list revisits that wire or reuses its
classical result cell. Covering the actual physical wires therefore gives the
zero basis operator tensored with the original external-reference marginal.

These equations concern the full quantum-reference marginal. They do not
discard any runtime cell, and do not identify the remaining classical blocks
or assert independence from stored classical results.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

variable {services : ClassicalOracleModel}

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
  {environment : (ExecutionModel.quantum gates oracles .empty services).Environment}

variable (implementations : ∀ wire,
  QuditShift.Realizations gates oracles ctx.quantumLayout wire)

/-- The reset matrix depends on the actual incoming quantum-reference marginal. -/
lemma zReset_execute_marginal_entry {allowAllocation : Bool} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History))
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
    ((circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations).execute environment Reference
      state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) =
      if left wire = ctx.quantumLayout.zeroLabel wire ∧
          right wire = ctx.quantumLayout.zeroLabel wire then
        ∑ outcome : Fin (ctx.quantumLayout.wire wire).dimension,
          state.quantumMarginal.matrix (Function.update left wire outcome, leftRef)
            (Function.update right wire outcome, rightRef)
      else 0 := by
  rw [zReset_execute_entry (allowAllocation := allowAllocation)]
  split
  · simp only [ExecutionState.quantumMarginal, Matrix.sum_apply]
    exact Finset.sum_comm
  · rfl

/-- A reset preserves zero support at any previously zero physical wire. -/
lemma zReset_execute_preserves_zero {allowAllocation : Bool} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (target : Fin ctx.systemCount) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History))
    (wasZero : ∀ (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index),
      (left target ≠ ctx.quantumLayout.zeroLabel target ∨
        right target ≠ ctx.quantumLayout.zeroLabel target) →
      state.quantumMarginal.matrix (left, leftRef) (right, rightRef) = 0)
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index)
    (nonzero : left target ≠ ctx.quantumLayout.zeroLabel target ∨
      right target ≠ ctx.quantumLayout.zeroLabel target) :
    ((circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations).execute environment Reference
      state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) = 0 := by
  rw [zReset_execute_marginal_entry (allowAllocation := allowAllocation)]
  by_cases same : target = wire
  · subst target
    rcases nonzero with leftNonzero | rightNonzero <;> simp_all
  · split
    · apply Finset.sum_eq_zero
      intro outcome _
      apply wasZero
      simpa only [Function.update_of_ne same] using nonzero
    · rfl

/-- Later actual resets preserve the zero support of a previously reset wire. -/
lemma zReset_sequence_preserves_zero {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (target : Fin ctx.systemCount) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History))
    (wasZero : ∀ (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index),
      (left target ≠ ctx.quantumLayout.zeroLabel target ∨
        right target ≠ ctx.quantumLayout.zeroLabel target) →
      state.quantumMarginal.matrix (left, leftRef) (right, rightRef) = 0)
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index)
    (nonzero : left target ≠ ctx.quantumLayout.zeroLabel target ∨
      right target ≠ ctx.quantumLayout.zeroLabel target) :
    ((sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts).execute environment Reference
      state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) = 0 := by
  induction readouts generalizing History with
  | nil =>
      rw [sequence_nil_quantumMarginal (allowAllocation := allowAllocation)]
      exact wasZero left right leftRef rightRef nonzero
  | cons head tail ih =>
      rw [sequence, Circuit.execute_seq,
          State.mapHistory_quantumMarginal]
      apply ih
      exact zReset_execute_preserves_zero (allowAllocation := allowAllocation) head.wire head.output
        (implementations head.wire) target state wasZero

/-- Every wire actually named in the reset list is zero at the end. -/
lemma zReset_sequence_member_zero {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (target : Fin ctx.systemCount) (present : target ∈ readouts.map ZReadout.wire)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History))
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index)
    (nonzero : left target ≠ ctx.quantumLayout.zeroLabel target ∨
      right target ≠ ctx.quantumLayout.zeroLabel target) :
    ((sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts).execute environment Reference
      state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) = 0 := by
  induction readouts generalizing History with
  | nil => simp at present
  | cons head tail ih =>
      rw [sequence, Circuit.execute_seq,
          State.mapHistory_quantumMarginal]
      rcases List.mem_cons.mp present with first | later
      · subst target
        apply zReset_sequence_preserves_zero (allowAllocation := allowAllocation) implementations
            tail head.wire
        · intro row column rowRef columnRef outside
          rw [zReset_execute_marginal_entry (allowAllocation := allowAllocation)]
          rcases outside with leftNonzero | rightNonzero <;> simp_all
        · exact nonzero
      · exact ih later ((circuit (allowAllocation := allowAllocation) (services := services)
          head.wire head.output
          (implementations head.wire)).execute environment Reference state)

/-- Resetting every actual wire gives zero tensored with the original reference marginal.
The coverage premise is a layout condition on the chosen internal reset list. -/
lemma zReset_sequence_complete_entry {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (covers : ∀ wire : Fin ctx.systemCount, wire ∈ readouts.map ZReadout.wire)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History))
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
    ((sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts).execute environment Reference
      state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          state.quantumMarginal.matrix (basis, leftRef) (basis, rightRef)
      else 0 := by
  have outside (row column : ctx.quantumLayout.Basis)
      (nonzero : row ≠ ctx.quantumLayout.zeroLabel ∨ column ≠ ctx.quantumLayout.zeroLabel) :
      ((sequence (allowAllocation := allowAllocation) (services := services) implementations
          readouts).execute environment Reference
        state).quantumMarginal.matrix
        (row, leftRef) (column, rightRef) = 0 := by
    rcases nonzero with leftNonzero | rightNonzero
    · obtain ⟨wire, differs⟩ := not_forall.mp (fun same => leftNonzero (funext same))
      exact zReset_sequence_member_zero (allowAllocation := allowAllocation) implementations
          readouts wire (covers wire) state
        row column leftRef rightRef (Or.inl differs)
    · obtain ⟨wire, differs⟩ := not_forall.mp (fun same => rightNonzero (funext same))
      exact zReset_sequence_member_zero (allowAllocation := allowAllocation) implementations
          readouts wire (covers wire) state
        row column leftRef rightRef (Or.inr differs)
  by_cases bothZero : left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel
  · rw [if_pos bothZero, bothZero.1, bothZero.2]
    have finalSum : (∑ basis : ctx.register.Index,
        ((sequence (allowAllocation := allowAllocation) (services := services) implementations
            readouts).execute environment Reference
          state).quantumMarginal.matrix
          (basis, leftRef) (basis, rightRef)) =
        ((sequence (allowAllocation := allowAllocation) (services := services) implementations
            readouts).execute environment Reference
          state).quantumMarginal.matrix
          (ctx.quantumLayout.zeroLabel, leftRef) (ctx.quantumLayout.zeroLabel, rightRef) := by
      apply Finset.sum_eq_single ctx.quantumLayout.zeroLabel
      · intro basis _ different
        exact outside basis basis (Or.inl different)
      · simp
    exact finalSum.symm.trans
      (zReset_sequence_reference_entry (allowAllocation := allowAllocation) implementations readouts
          state leftRef rightRef)
  · rw [if_neg bothZero]
    exact outside left right (not_and_or.mp bothZero)

end

end QuantumAlg.ZReset
