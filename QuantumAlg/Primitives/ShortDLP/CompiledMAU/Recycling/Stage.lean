/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Preparation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Reset
import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Operations
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Complete record-conditioned Kraus matrix of one actual recycled-control stage

The preparation operator is the literal
H/arithmetic/stored-feedback/H prefix. Its reset row is derived from the
existing measured reset's exact matrix equation. All physical wires remain
in the matrix; no input state, caller store, reference or history is restricted.
The one output write may overwrite a previously correlated value. Distinct
canonical output cells are needed later to retain all n writes simultaneously.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Reassociate actual sequential records, without discarding a history coordinate. -/
private def recordAssociation (History Left Right : Type) :
    (Store (Context base noQuantum m ell width) ×
      (model.HiddenState × ((History × Left) × Right))) ≃
    (Store (Context base noQuantum m ell width) ×
      (model.HiddenState × (History × (Left × Right)))) :=
  (Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr (Equiv.prodAssoc _ _ _))

/-- Complete premeasurement record, computed from the original store. -/
def preparationRecord (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits) {History : Type}
    (source : Store (Context base noQuantum m ell width) × (model.HiddenState × History)) :
    Store (Context base noQuantum m ell width) ×
      (model.HiddenState ×
        (History × (stagePreparation base noQuantum m ell width inverse outputs N unit
          position).Path)) :=
  (source.1, (source.2.1, (source.2.2,
    preparationPath base noQuantum m ell width inverse outputs N unit position source.1)))

/-- The actual output write, feedback/reset branches and original history share one record. -/
def stageRecord (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits) {History : Type}
    (source : Store (Context base noQuantum m ell width) × (model.HiddenState × History))
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    Store (Context base noQuantum m ell width) ×
      (model.HiddenState ×
        (History × (stage base noQuantum m ell width inverse outputs N unit position).Path)) :=
  recordAssociation base noQuantum m ell width History _ _
    (resetRecord base noQuantum m ell width (outputs position)
      (preparationRecord base noQuantum m ell width inverse outputs N unit position source)
      outcome)

/-- Partial-isometry row of the real measured-reset branch.
Partner/reference coordinates persist. -/
def resetRow (Reference : Register)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    HilbertOperator ((Context base noQuantum m ell width).register.prod Reference) :=
  fun row column =>
    if row.1 (control base noQuantum m ell width) = 0 ∧
        column = (Function.update row.1 (control base noQuantum m ell width) outcome, row.2)
      then 1 else 0

private lemma resetRow_mul (Reference : Register)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension)
    (matrix : HilbertOperator ((Context base noQuantum m ell width).register.prod Reference))
    (row column : ((Context base noQuantum m ell width).register.prod Reference).Index) :
    (resetRow base noQuantum m ell width Reference outcome * matrix) row column =
      if row.1 (control base noQuantum m ell width) = 0 then
        matrix (Function.update row.1 (control base noQuantum m ell width) outcome, row.2) column
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases zero : row.1 (control base noQuantum m ell width) = 0
  · simp only [resetRow, zero, true_and, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [resetRow, zero, false_and, if_false, zero_mul, Finset.sum_const_zero]

/-- This is the exact all-entry conjugation of the observed reset, not only a Born marginal. -/
private lemma resetRow_conjugation (Reference : Register)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension)
    (matrix : HilbertOperator ((Context base noQuantum m ell width).register.prod Reference))
    (row column : ((Context base noQuantum m ell width).register.prod Reference).Index) :
    (resetRow base noQuantum m ell width Reference outcome * matrix *
      (resetRow base noQuantum m ell width Reference outcome).conjTranspose) row column =
    if row.1 (control base noQuantum m ell width) = 0 ∧
        column.1 (control base noQuantum m ell width) = 0 then
      matrix (Function.update row.1 (control base noQuantum m ell width) outcome, row.2)
        (Function.update column.1 (control base noQuantum m ell width) outcome, column.2)
    else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [resetRow_mul, Matrix.conjTranspose_apply]
  by_cases leftZero : row.1 (control base noQuantum m ell width) = 0 <;>
    by_cases rightZero : column.1 (control base noQuantum m ell width) = 0 <;>
    simp only [resetRow, leftZero, rightZero, true_and, false_and, and_true, and_false,
      if_true, if_false, apply_ite, star_one, star_zero, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, Finset.sum_const_zero]

/-- Actual one-bit branch operator, built from the native prefix and measured-reset row. -/
def stageKraus (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits) (Reference : Register)
    (store : Store (Context base noQuantum m ell width))
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    HilbertOperator ((Context base noQuantum m ell width).register.prod Reference) :=
  resetRow base noQuantum m ell width Reference outcome *
    (preparationAction (environment := environment) base noQuantum m ell width inverse outputs
      N unit position Reference
      store : HilbertOperator ((Context base noQuantum m ell width).register.prod Reference))

/-- Full actual instrument on every classical/service/history and quantum/reference entry.
All branch operators are derived above; the theorem assumes no supplied channel equation. -/
lemma stage_block_entry (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (entry : Store (Context base noQuantum m ell width) ×
      (model.HiddenState ×
        (History × (stage base noQuantum m ell width inverse outputs N unit position).Path)))
    (row column : ((Context base noQuantum m ell width).register.prod Reference).Index) :
    (((stage base noQuantum m ell width inverse outputs N unit position).execute environment
        Reference state).block entry).matrix row column =
      ∑ source : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
            (control base noQuantum m ell width)).dimension,
          if stageRecord base noQuantum m ell width inverse outputs N unit position source
              outcome = entry then
            let operator := stageKraus (environment := environment) base noQuantum m ell
              width inverse outputs N unit position
              Reference source.1 outcome
            (operator * (state.block source).matrix * operator.conjTranspose) row column
          else 0 := by
  let prepared := stagePreparation base noQuantum m ell width inverse outputs N unit position
  let reset := measuredReset base noQuantum m ell width (outputs position)
  let association := recordAssociation base noQuantum m ell width History prepared.Path reset.Path
  let nested := association.symm entry
  let acted (source : Store (Context base noQuantum m ell width) ×
      (model.HiddenState × History)) :=
    (preparationAction (environment := environment) base noQuantum m ell width inverse outputs
      N unit position Reference
      source.1 : HilbertOperator ((Context base noQuantum m ell width).register.prod Reference)) *
      (state.block source).matrix *
      (preparationAction (environment := environment) base noQuantum m ell width inverse
        outputs N unit position Reference
        source.1 : HilbertOperator
          ((Context base noQuantum m ell width).register.prod Reference)).conjTranspose
  have executed :
      (((stage base noQuantum m ell width inverse outputs N unit position).execute environment
          Reference state).block entry).matrix row column =
        ((reset.execute environment Reference (prepared.execute environment Reference
          state)).block nested).matrix
          row column :=
    (congrArg
      (fun evolved : State (Context base noQuantum m ell width) Reference
          (model.HiddenState × (History × (prepared.seq reset).Path)) =>
        (evolved.block entry).matrix row column)
      (Circuit.execute_seq (environment := environment) prepared reset state)).trans
      (State.mapHistory_equiv_entry
        (reset.execute environment Reference (prepared.execute environment Reference state))
        ((Equiv.refl model.HiddenState).prodCongr
          (Equiv.prodAssoc History prepared.Path reset.Path))
        entry.1 entry.2 row column)
  have preparedMatrix (middle : Store (Context base noQuantum m ell width) ×
      (model.HiddenState × (History × prepared.Path))) :
      ((prepared.execute environment Reference state).block middle).matrix =
        ∑ source : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
          if preparationRecord base noQuantum m ell width inverse outputs N unit position
              source = middle then acted source else 0 :=
    congrArg
      (fun evolved : State (Context base noQuantum m ell width) Reference
          (model.HiddenState × (History × prepared.Path)) => (evolved.block middle).matrix)
      (stagePreparation_execute base noQuantum m ell width inverse outputs N unit position state)
  have preparedEntry (middle : Store (Context base noQuantum m ell width) ×
      (model.HiddenState × (History × prepared.Path)))
      (left right : ((Context base noQuantum m ell width).register.prod Reference).Index) :
      ((prepared.execute environment Reference state).block middle).matrix left right =
        ∑ source : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
          if preparationRecord base noQuantum m ell width inverse outputs N unit position
              source = middle then acted source left right else 0 :=
    (congrArg
      (fun matrix : HilbertOperator
          ((Context base noQuantum m ell width).register.prod Reference) =>
        matrix left right) (preparedMatrix middle)).trans (by
          simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply])
  refine executed.trans ((measuredReset_block_entry base noQuantum m ell width (outputs position)
    (prepared.execute environment Reference state) nested row.1 column.1 row.2 column.2).trans ?_)
  trans ∑ middle : Store (Context base noQuantum m ell width) ×
      (model.HiddenState × (History × prepared.Path)),
    ∑ outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
        (control base noQuantum m ell width)).dimension,
      if resetRecord base noQuantum m ell width (outputs position) middle outcome = nested then
        if row.1 (control base noQuantum m ell width) = 0 ∧
            column.1 (control base noQuantum m ell width) = 0 then
          (∑ source : Store (Context base noQuantum m ell width) ×
              (model.HiddenState × History),
            if preparationRecord base noQuantum m ell width inverse outputs N unit position
                source = middle then
              acted source
                (Function.update row.1 (control base noQuantum m ell width) outcome, row.2)
                (Function.update column.1 (control base noQuantum m ell width) outcome, column.2)
            else 0) else 0 else 0
  · apply Finset.sum_congr rfl
    intro middle _
    apply Finset.sum_congr rfl
    intro outcome _
    by_cases selected : resetRecord base noQuantum m ell width (outputs position)
        middle outcome = nested
    · by_cases zero : row.1 (control base noQuantum m ell width) = 0 ∧
          column.1 (control base noQuantum m ell width) = 0
      · simpa only [if_pos selected, if_pos zero] using
          (preparedEntry middle
            (Function.update row.1 (control base noQuantum m ell width) outcome, row.2)
            (Function.update column.1 (control base noQuantum m ell width) outcome, column.2))
      · simp only [if_pos selected, if_neg zero]
    · simp only [if_neg selected]
  · have distribute (middle : Store (Context base noQuantum m ell width) ×
        (model.HiddenState × (History × prepared.Path)))
        (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
          (control base noQuantum m ell width)).dimension) :
        (if resetRecord base noQuantum m ell width (outputs position) middle outcome = nested then
          if row.1 (control base noQuantum m ell width) = 0 ∧
              column.1 (control base noQuantum m ell width) = 0 then
            (∑ source : Store (Context base noQuantum m ell width) ×
                (model.HiddenState × History),
              if preparationRecord base noQuantum m ell width inverse outputs N unit position
                  source = middle then
                acted source
                  (Function.update row.1 (control base noQuantum m ell width) outcome, row.2)
                  (Function.update column.1 (control base noQuantum m ell width) outcome, column.2)
              else 0) else 0 else 0) =
        ∑ source : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
          if preparationRecord base noQuantum m ell width inverse outputs N unit position
              source = middle then
            if resetRecord base noQuantum m ell width (outputs position) middle outcome = nested
              then
              if row.1 (control base noQuantum m ell width) = 0 ∧
                  column.1 (control base noQuantum m ell width) = 0 then
                acted source
                  (Function.update row.1 (control base noQuantum m ell width) outcome, row.2)
                  (Function.update column.1 (control base noQuantum m ell width) outcome, column.2)
              else 0 else 0 else 0 := by
      by_cases selected : resetRecord base noQuantum m ell width (outputs position) middle
          outcome = nested <;>
        by_cases zero : row.1 (control base noQuantum m ell width) = 0 ∧
          column.1 (control base noQuantum m ell width) = 0 <;>
        simp only [selected, zero, and_self, if_true, if_false, ite_self,
          Finset.sum_const_zero]
    simp_rw [distribute]
    rw [Finset.sum_comm]
    have exchange :
        (∑ outcome, ∑ middle, ∑ source,
          if preparationRecord base noQuantum m ell width inverse outputs N unit position
              source = middle then
            if resetRecord base noQuantum m ell width (outputs position) middle outcome = nested
              then
              if row.1 (control base noQuantum m ell width) = 0 ∧
                  column.1 (control base noQuantum m ell width) = 0 then
                acted source
                  (Function.update row.1 (control base noQuantum m ell width) outcome, row.2)
                  (Function.update column.1 (control base noQuantum m ell width) outcome, column.2)
              else 0 else 0 else 0) =
        ∑ source, ∑ outcome,
          if resetRecord base noQuantum m ell width (outputs position)
              (preparationRecord base noQuantum m ell width inverse outputs N unit position source)
              outcome = nested then
            if row.1 (control base noQuantum m ell width) = 0 ∧
                column.1 (control base noQuantum m ell width) = 0 then
              acted source
                (Function.update row.1 (control base noQuantum m ell width) outcome, row.2)
                (Function.update column.1 (control base noQuantum m ell width) outcome, column.2)
            else 0 else 0 := by
      conv_lhs =>
        arg 2
        ext outcome
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro outcome _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [exchange]
    apply Finset.sum_congr rfl
    intro source _
    apply Finset.sum_congr rfl
    intro outcome _
    have selected : stageRecord base noQuantum m ell width inverse outputs N unit position
        source outcome = entry ↔
        resetRecord base noQuantum m ell width (outputs position)
          (preparationRecord base noQuantum m ell width inverse outputs N unit position source)
          outcome = nested := (association.eq_symm_apply).symm
    by_cases taken : stageRecord base noQuantum m ell width inverse outputs N unit position
        source outcome = entry
    · simp only [if_pos taken, if_pos (selected.mp taken), stageKraus,
        Matrix.conjTranspose_mul, Matrix.mul_assoc]
      simpa only [acted, Matrix.mul_assoc] using
        (resetRow_conjugation base noQuantum m ell width Reference outcome
          (acted source) row column).symm
    · simp only [if_neg taken, if_neg (fun found => taken (selected.mpr found))]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling
