/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Preservation
import all QuantumAlg.Core.Execution.State.Marginal
import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Encoding

/-!
# Joint classical-spectator and external-reference observations

The retained classical label indexes the complete external-reference matrix.
Local systems and inaccessible service records are summed within that same
label, preserving every classical-quantum correlation. Orthogonal reference
tags give the identical observation without normalizing any slice
[dW19, qcnotes.tex:5381,5394,6827].
-/

namespace QuantumAlg

noncomputable section

attribute [local instance] Classical.decEq

namespace ExecutionState

variable {C D E : Type} [Fintype C] [Fintype D] [Fintype E]
  {R Reference : Register}

/-- Observe a finite classical label jointly with the complete untouched reference. -/
def referenceObservation (state : ExecutionState C (R.prod Reference)) (read : C → D) :
    ExecutionState D Reference :=
  ((state.mapClassical read).reindex
    (S := Reference.prod R) (Equiv.prodComm R.Index Reference.Index)).marginalLeft

/-- Each observed label contains the entire reference matrix of its original fiber. -/
lemma referenceObservation_entry (state : ExecutionState C (R.prod Reference))
    (read : C → D) (label : D) (row column : Reference.Index) :
    ((state.referenceObservation read).block label).matrix row column =
      ∑ basis : R.Index, ∑ record : C,
        if read record = label then
          (state.block record).matrix (basis, row) (basis, column) else 0 := by
  simp only [referenceObservation, executionState_marginalLeft_entry,
    reindex_block_entry, mapClassical_block_matrix, Matrix.sum_apply,
    Matrix.ite_apply, Matrix.zero_apply]
  rfl

/-- This observation retains total mass without conditioning on the spectator value. -/
lemma referenceObservation_mass (state : ExecutionState C (R.prod Reference))
    (read : C → D) : (state.referenceObservation read).mass = state.mass :=
  (executionState_marginalLeft_mass _).trans
    ((reindex_mass _ _).trans (mapClassical_mass state read))

/-- Regrouping complete classical coordinates commutes with the same spectator observation. -/
lemma referenceObservation_mapClassical [DecidableEq D]
    (state : ExecutionState C (R.prod Reference))
    (update : C → D) (read : D → E) :
    (state.mapClassical update).referenceObservation read =
      state.referenceObservation (read ∘ update) := by
  simp only [referenceObservation,
    executionState_mapClassical_comp_instances (result := Classical.decEq _)]

end ExecutionState

namespace Execution.State

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {Hidden H Path : Type} [Fintype Hidden] [Fintype H] [Fintype Path]

/-- The encoded input's diagonal tag block retains the complete spectator-reference law. -/
lemma referenceObservation_encodeOracleTag_entry
    (state : State ctx Reference (Hidden × (H × Tag.Index)))
    (tag : Tag.Index) (row column : Reference.Index) :
    ((state.referenceObservation (fun record => record.2.2.2)).block tag).matrix row column =
      (encodeOracleTag state).referenceMarginal.matrix (tag, row) (tag, column) := by
  simp only [ExecutionState.referenceObservation_entry,
    ExecutionState.referenceMarginal_entry, ExecutionState.quantumMarginal,
    Matrix.sum_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro basis _
  apply Finset.sum_congr rfl
  intro store _
  apply Finset.sum_congr rfl
  intro hidden _
  apply Finset.sum_congr rfl
  intro history _
  let : DecidableEq Tag.Index := Classical.decEq _
  exact (Fintype.sum_ite_eq' tag (fun actualTag : Tag.Index =>
    (state.block (store, (hidden, (history, actualTag)))).matrix
      (basis, row) (basis, column))).trans
    (((encodeOracleTag_entry state store hidden history tag tag
      (basis, row) (basis, column)).trans (if_pos rfl)).symm)

/-- Decoding the final tag retains the same entire reference matrix at each spectator value. -/
lemma referenceObservation_decodeExecutionTag_entry
    (state : State ctx (Tag.prod Reference) (Hidden × (H × Path)))
    (tag : Tag.Index) (row column : Reference.Index) :
    (((decodeExecutionTag state).referenceObservation
      (fun record => record.2.2.1.2)).block tag).matrix row column =
      state.referenceMarginal.matrix (tag, row) (tag, column) := by
  simp only [ExecutionState.referenceObservation_entry,
    ExecutionState.referenceMarginal_entry, ExecutionState.quantumMarginal,
    Matrix.sum_apply, Fintype.sum_prod_type, decodeExecutionTag_entry]
  apply Finset.sum_congr rfl
  intro basis _
  apply Finset.sum_congr rfl
  intro store _
  apply Finset.sum_congr rfl
  intro hidden _
  apply Finset.sum_congr rfl
  intro history _
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Execution.State

end

end QuantumAlg
