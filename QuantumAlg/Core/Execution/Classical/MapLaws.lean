/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Measure.Instrument

/-!
# Finite classical maps through actual quantum block operations

Noninjective classical maps sum every source density block in their fiber.
The existing Z update, stored-value selection and admissible finite sum
commute with those sums. All matrix entries are retained, including their
off-diagonal reference coordinates [dW19, qcnotes.tex:5381,5409].
-/

namespace QuantumAlg.ExecutionState

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {C D O I : Type} [Fintype C] [Fintype D] [Fintype O] [Fintype I]
  {R : Register}

/-- Relabeling prior classical records commutes with the existing full Z poststate. -/
lemma mapClassical_measureZ [DecidableEq D] [DecidableEq O] [DecidableEq (D × O)]
    (state : ExecutionState C R) (update : C → D)
    (readout : R.Index → O) :
    (state.mapClassical update).measureZ readout =
      (state.measureZ readout).mapClassical (fun value => (update value.1, value.2)) := by
  apply ExecutionState.ext
  rintro ⟨result, outcome⟩
  apply DensityOperator.ext
  ext row column
  simp only [measureZ_block, ZMeasurement.branch_matrix, mapClassical_block_matrix,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, Fintype.sum_prod_type]
  have inner (value : C) :
      (∑ other : O, if (update value, other) = (result, outcome) then
        (if readout row = other ∧ readout column = other then
          (state.block value).matrix row column else 0) else 0) =
      if update value = result then
        (if readout row = outcome ∧ readout column = outcome then
          (state.block value).matrix row column else 0) else 0 := by
    by_cases selected : update value = result <;> simp [selected]
  simp_rw [inner]
  by_cases selected : readout row = outcome ∧ readout column = outcome <;> simp [selected]

omit [Fintype O] in
/-- A selection after a classical map selects exactly its original source fibers. -/
lemma mapClassical_selectClassical [DecidableEq D] [DecidableEq O]
    (state : ExecutionState C R) (update : C → D)
    (readout : D → O) (selected : O) :
    (state.mapClassical update).selectClassical readout selected =
      (state.selectClassical (readout ∘ update) selected).mapClassical update := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  simp only [selectClassical_block, apply_ite DensityOperator.matrix,
    DensityOperator.zero_matrix, mapClassical_block_matrix, Function.comp_apply]
  have distribute :
      (if readout result = selected then
        (∑ value : C, if update value = result then (state.block value).matrix else 0) else 0) =
      ∑ value : C, if readout result = selected then
        (if update value = result then (state.block value).matrix else 0) else 0 := by
    by_cases active : readout result = selected <;> simp [active]
  refine distribute.trans (Finset.sum_congr rfl fun value _ => ?_)
  by_cases matching : update value = result <;> simp [matching]

/-- Classical fiber sums commute with the actual admissible finite sum of states. -/
lemma mapClassical_finiteSum [DecidableEq D] (states : I → ExecutionState C R)
    (total : ∑ index, (states index).mass ≤ 1) (update : C → D) :
    (finiteSum states total).mapClassical update =
      finiteSum (fun index => (states index).mapClassical update)
        (by simpa only [mapClassical_mass] using total) := by
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  simp only [mapClassical_block_matrix, finiteSum_block_matrix]
  have distribute (value : C) :
      (if update value = result then
        (∑ index : I, ((states index).block value).matrix) else 0) =
      ∑ index : I, if update value = result then ((states index).block value).matrix else 0 := by
    by_cases active : update value = result <;> simp [active]
  simp_rw [distribute]
  exact Finset.sum_comm

end

end QuantumAlg.ExecutionState
