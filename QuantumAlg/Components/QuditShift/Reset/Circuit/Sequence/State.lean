/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Semantics

/-!
# Complete actual blocks after finite reset-to-basis execution

Each actual stage establishes its prescribed wire value and preserves every
previously established wire value. This holds for arbitrary original stores,
histories and reference correlations, including zero-mass blocks. The complete
finite sequence therefore factors the prescribed local basis ket out of every
actual final record while retaining that record's full reference coefficient.
No outcomes are deleted, no result cell is assumed fresh, and no initial basis
support is supplied by the caller.
-/

namespace QuantumAlg.QuditShift

noncomputable section

open Execution
open scoped ComplexOrder

local instance {α : Type} : DecidableEq α := Classical.decEq α

private instance sequenceStateDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {gates : GateModel} {oracles : OracleModel}
variable {ctx : RuntimeCtx .quantum}

variable {implementations : ∀ wire,
  Realizations gates oracles ctx.quantumLayout wire}

private def WireSupported (wire : Fin ctx.systemCount)
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) : Prop :=
  ∀ record left right (refLeft refRight : Reference.Index), left wire ≠ value →
    (state.block record).matrix (left, refLeft) (right, refRight) = 0

private theorem supported_mapHistory (wire : Fin ctx.systemCount)
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    {Reference : Register} {History Later : Type} [Fintype History] [Fintype Later]
    (state : State ctx Reference History) (update : History → Later)
    (supported : WireSupported wire value state) :
    WireSupported wire value (state.mapHistory update) := by
  intro result left right refLeft refRight different
  change ((state.mapClassical _).block result).matrix _ _ = 0
  rw [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro record _
  split_ifs
  · exact supported record left right refLeft refRight different
  · rfl

private theorem supported_sequence (wire : Fin ctx.systemCount)
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (first second : Circuit (.quantum gates oracles) ctx ctx) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (supported : WireSupported wire value
      (second.execute Reference (first.execute Reference state))) :
    WireSupported wire value ((first.seq second).execute Reference state) := by
  exact Eq.mpr (congrArg (WireSupported wire value) (Circuit.execute_seq first second state))
    (supported_mapHistory wire value _ _ supported)

private theorem resetWireToBasis_supported (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History)) :
    WireSupported wire value ((resetWireToBasis wire (implementations wire) output value).execute
      Reference state) := by
  intro result left right refLeft refRight different
  rw [resetWireToBasis_block_entry]
  simp only [different, false_and, if_false, ite_self, Finset.sum_const_zero]

private theorem resetWireToBasis_preserves (wire focus : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (supported : WireSupported focus (label focus) state) :
    WireSupported focus (label focus)
      ((resetWireToBasis wire (implementations wire) output (label wire)).execute Reference state)
        := by
  by_cases same : focus = wire
  · subst focus
    exact resetWireToBasis_supported (implementations := implementations) wire output (label wire)
      state
  · intro result left right refLeft refRight outside
    rw [resetWireToBasis_block_entry]
    apply Finset.sum_eq_zero
    intro record _
    apply Finset.sum_eq_zero
    intro outcome _
    have zero := supported record (Function.update left wire outcome)
      (Function.update right wire outcome) refLeft refRight (by
        simpa only [Function.update_of_ne same] using outside)
    simp only [zero, ite_self]

private theorem resetToBasisOn_preserves (count : Nat)
    (wires : Fin count → Fin ctx.systemCount)
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) (focus : Fin ctx.systemCount)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (supported : WireSupported focus (label focus) state) :
    WireSupported focus (label focus)
      ((resetToBasisOn implementations count wires outputs label).execute Reference state) := by
  induction count generalizing History with
  | zero =>
      intro record left right refLeft refRight different
      rcases record with ⟨store, hidden, history, path⟩
      cases path
      change (((Circuit.id (model := .quantum gates oracles) ctx).execute
        Reference state).block (store, (hidden, (history, ())))).matrix
          (left, refLeft) (right, refRight) = 0
      rw [Circuit.execute_id_block]
      exact supported (store, (hidden, history)) left right refLeft refRight different
  | succ count ih =>
      apply supported_sequence focus (label focus)
        (resetWireToBasis (wires 0) (implementations (wires 0)) (outputs (wires 0)) (label (wires
          0)))
        (resetToBasisOn implementations count (fun index => wires index.succ) outputs label) state
      exact ih _ _ (resetWireToBasis_preserves (implementations := implementations) (wires 0)
        focus (outputs (wires 0))
        label state supported)

private theorem resetToBasisOn_supported (count : Nat)
    (wires : Fin count → Fin ctx.systemCount)
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (index : Fin count) :
    WireSupported (wires index) (label (wires index))
      ((resetToBasisOn implementations count wires outputs label).execute Reference state) := by
  induction count generalizing History with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun next => ?_) index
      · apply supported_sequence (wires 0) (label (wires 0))
          (resetWireToBasis (wires 0) (implementations (wires 0)) (outputs (wires 0)) (label
            (wires 0)))
          (resetToBasisOn implementations count (fun index => wires index.succ) outputs label) state
        exact resetToBasisOn_preserves (implementations := implementations) count (fun index =>
          wires index.succ) outputs label
          (wires 0) _ (resetWireToBasis_supported (implementations := implementations) (wires 0)
            (outputs (wires 0))
            (label (wires 0)) state)
      · apply supported_sequence (wires next.succ) (label (wires next.succ))
          (resetWireToBasis (wires 0) (implementations (wires 0)) (outputs (wires 0)) (label
            (wires 0)))
          (resetToBasisOn implementations count (fun index => wires index.succ) outputs label) state
        exact ih _ _ next

/-- Every complete actual final record has exactly the prescribed local basis support. -/
theorem resetToBasis_block_entry
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (record : Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState ×
      (History × (resetToBasis implementations outputs label).Path)))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index) :
    (((resetToBasis implementations outputs label).execute Reference state).block record).matrix
        (left, refLeft) (right, refRight) =
      if left = label ∧ right = label then
        (((resetToBasis implementations outputs label).execute Reference state).block record).matrix
          (label, refLeft) (label, refRight)
      else 0 := by
  have rowZero (row : ctx.quantumLayout.Basis) (outside : row ≠ label)
      (column : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
      (((resetToBasis implementations outputs label).execute Reference state).block record).matrix
        (row, leftRef) (column, rightRef) = 0 := by
    obtain ⟨wire, different⟩ : ∃ wire, row wire ≠ label wire := by
      by_contra absent
      push Not at absent
      exact outside (funext absent)
    exact resetToBasisOn_supported (implementations := implementations) ctx.systemCount id outputs
      label state wire
      record row column leftRef rightRef different
  by_cases sameLeft : left = label
  · subst left
    by_cases sameRight : right = label
    · subst right
      simp only [and_self, if_true]
    · simp only [sameRight, and_false, if_false]
      have hermitian :=
        (((resetToBasis implementations outputs label).execute Reference state).block
          record).positive.isHermitian
      rw [← hermitian.apply (label, refLeft) (right, refRight),
        rowZero right sameRight label refRight refLeft, star_zero]
  · simp only [sameLeft, false_and, if_false]
    exact rowZero left sameLeft right refLeft refRight

/-- The prescribed ket factors from each actual record's full conditional reference coefficient. -/
theorem resetToBasis_block_factor
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (record : Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState ×
      (History × (resetToBasis implementations outputs label).Path)))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index) :
    (((resetToBasis implementations outputs label).execute Reference state).block record).matrix
        (left, refLeft) (right, refRight) =
      NormalizedVector.ket (R := ctx.register) label left *
        (((resetToBasis implementations outputs label).execute Reference state).block record).matrix
          (label, refLeft) (label, refRight) *
        star (NormalizedVector.ket (R := ctx.register) label right) :=
  (resetToBasis_block_entry (implementations := implementations) outputs label state record left
    right refLeft refRight).trans
    (BasisSeeded.ket_factor (R := ctx.register) label left right _).symm

end

end QuantumAlg.QuditShift
