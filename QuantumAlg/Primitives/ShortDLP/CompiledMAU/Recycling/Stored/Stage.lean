/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Stored.Outputs
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Store.Blocks

/-!
# Actual one-stage instrument on complete stored blocks

This derives the stored matrix formula
from the complete actual stage records, retaining arbitrary dirty physical
input, mixed reference and original Store/hidden/history correlations. Summing
an internal record is a mathematical observation, not a storage instruction.
The store-dependent branch operators come from the actual native preparation
and measured reset. No caller-supplied instrument equation is a premise.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.StoredStage

noncomputable section

open Execution

variable {environment : model.Environment}
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma sum_records {Source Entry Outcome Value : Type}
    [Fintype Source] [Fintype Entry] [Fintype Outcome] [entryDecision : DecidableEq Entry]
    (record : Source → Outcome → Entry) (read : Entry → Value) (value : Value)
    (contribution : Source → Outcome → ℂ) :
    (∑ entry : Entry, if read entry = value then
      ∑ source : Source, ∑ outcome : Outcome,
        if record source outcome = entry then contribution source outcome else 0
      else 0) =
      ∑ source : Source, ∑ outcome : Outcome,
        if read (record source outcome) = value then contribution source outcome else 0 := by
  have distribute (entry : Entry) :
      (if read entry = value then ∑ source : Source, ∑ outcome : Outcome,
        if record source outcome = entry then contribution source outcome else 0 else 0) =
      ∑ source : Source, ∑ outcome : Outcome,
        if record source outcome = entry then
          (if read entry = value then contribution source outcome else 0) else 0 := by
    by_cases selected : read entry = value
    · simp only [if_pos selected]
    · simp only [if_neg selected, ite_self, Finset.sum_const_zero]
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [Finset.sum_eq_single (record source outcome)]
  · simp only [if_true]
  · intro other _ different
    simp only [if_neg (Ne.symm different)]
  · intro absent
    exact False.elim (absent (Finset.mem_univ _))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

private lemma store_block_sum {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference History)
    (stored : Store (Context base noQuantum m ell width)) :
    (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ history : History, (state.block (stored, history)).matrix := by
  rw [← BasisSeeded.store_matrix, ExecutionState.mapClassical_block_matrix,
    Fintype.sum_prod_type]
  change (∑ original : Store (Context base noQuantum m ell width),
    ∑ history : History,
      if original = stored then (state.block (original, history)).matrix else 0) = _
  rw [Finset.sum_eq_single stored]
  · simp only [if_true]
  · intro other _ different
    simp only [if_neg different, Finset.sum_const_zero]
  · intro absent
    exact False.elim (absent (Finset.mem_univ _))

/-- The actual complete stored branch sums exactly all original records and binary outcomes. -/
lemma stage_store_entry (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (stored : Store (Context base noQuantum m ell width))
    (row column : ((Context base noQuantum m ell width).register.prod Reference).Index) :
    (((stage base noQuantum m ell width inverse outputs N unit position).execute environment
      Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix) row column =
      ∑ source : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcome : Fin 2,
          if source.1.write (outputs position) (.finite outcome) = stored then
            let operator := stageKraus (environment := environment) base noQuantum m ell width
              inverse outputs N unit position
              Reference source.1 (ContextCoordinates.physicalBit base noQuantum m ell width outcome)
            (operator * (state.block source).matrix * operator.conjTranspose) row column
          else 0 := by
  rw [← BasisSeeded.store_matrix]
  simp only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply,
    Matrix.ite_apply, Matrix.zero_apply]
  simp_rw [stage_block_entry]
  let contribution
      (source : Store (Context base noQuantum m ell width) × (model.HiddenState × History))
      (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
        (control base noQuantum m ell width)).dimension) : ℂ :=
    let operator : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
        ((Context base noQuantum m ell width).register.prod Reference).Index ℂ :=
      stageKraus (environment := environment) base noQuantum m ell width inverse outputs N unit
        position Reference source.1
        outcome
    (operator * (state.block source).matrix * operator.conjTranspose) row column
  have summed := sum_records (entryDecision := instDecidableEqProd)
    (stageRecord base noQuantum m ell width inverse outputs N unit position)
    (fun entry => entry.1) stored contribution
  refine summed.trans ?_
  change (∑ source, ∑ outcome,
      if (stageRecord base noQuantum m ell width inverse outputs N unit position source
        outcome).1 = stored then contribution source outcome else 0) =
    ∑ source, ∑ outcome : Fin 2,
      if source.1.write (outputs position) (.finite outcome) = stored then
        contribution source
          (ContextCoordinates.physicalBit base noQuantum m ell width outcome)
      else 0
  apply Finset.sum_congr rfl
  intro source _
  let outcomes : Fin 2 ≃ Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension :=
    finCongr (congrArg PNat.val (control_qubit base noQuantum m ell width)).symm
  rw [← Equiv.sum_comp outcomes]
  apply Finset.sum_congr rfl
  intro outcome _
  change (if (stageRecord base noQuantum m ell width inverse outputs N unit position source
    (ContextCoordinates.physicalBit base noQuantum m ell width outcome)).1 = stored then
      contribution source (ContextCoordinates.physicalBit base noQuantum m ell width outcome)
    else 0) = _
  rw [StoredOutputs.stageRecord_store]

/-- The actual branch operator depends only on the original Store; every quantum block is full. -/
lemma stage_store_matrix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (stored : Store (Context base noQuantum m ell width)) :
    ((stage base noQuantum m ell width inverse outputs N unit position).execute environment
      Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store (Context base noQuantum m ell width), ∑ outcome : Fin 2,
        if original.write (outputs position) (.finite outcome) = stored then
          let operator := stageKraus (environment := environment) base noQuantum m ell width
            inverse outputs N unit position
            Reference original (ContextCoordinates.physicalBit base noQuantum m ell width outcome)
          operator *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              operator.conjTranspose
        else 0 := by
  ext row column
  rw [stage_store_entry]
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases selected : original.write (outputs position) (.finite outcome) = stored
  · simp only [if_pos selected]
    rw [store_block_sum base noQuantum m ell width]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  · simp only [if_neg selected, Finset.sum_const_zero]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.StoredStage
