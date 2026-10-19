/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.Coordinate.Transport
import all QuantumAlg.Core.Measure.Instrument

/-!
# Exact coordinate changes for the existing Z measurement update

The same computational-basis readout can be expressed in two exact basis
coordinate systems. Its full conditional matrix, classical input and measured
outcome are preserved by the corresponding bijections
[dW19, qcnotes.tex:5409,5420]. This is a law of the existing Z interpreter
update, without a new measurement family or execution mechanism.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D O P : Type} [Fintype C] [Fintype D] [Fintype O] [Fintype P]
  [DecidableEq D] [DecidableEq O] [DecidableEq P] {R S : Register}

/-- Exact readout coordinates retain the complete postmeasurement density block. -/
lemma coordinate_measureZ (state : ExecutionState C R)
    (basis : R.Index ≃ S.Index) (labels : C ≃ D) (outcomes : O ≃ P)
    (original : R.Index → O) (transported : S.Index → P)
    (reads : ∀ value, outcomes (original value) = transported (basis value)) :
    ((state.measureZ original).mapClassical (labels.prodCongr outcomes)).reindex basis =
      ((state.mapClassical labels).reindex basis).measureZ transported := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  have source := coordinate_transport_entry (state.measureZ original)
    (labels.prodCongr outcomes) basis value row column
  have target := coordinate_transport_entry state labels basis value.1 row column
  have rowRead : original (basis.symm row) = outcomes.symm (transported row) := by
    apply outcomes.injective
    simpa only [Equiv.apply_symm_apply] using reads (basis.symm row)
  have columnRead : original (basis.symm column) = outcomes.symm (transported column) := by
    apply outcomes.injective
    simpa only [Equiv.apply_symm_apply] using reads (basis.symm column)
  calc
    _ = (ZMeasurement.branch original (outcomes.symm value.2)
        (state.block (labels.symm value.1))).matrix (basis.symm row) (basis.symm column) :=
      source
    _ = if original (basis.symm row) = outcomes.symm value.2 ∧
        original (basis.symm column) = outcomes.symm value.2 then
          (state.block (labels.symm value.1)).matrix (basis.symm row) (basis.symm column)
        else 0 := ZMeasurement.branch_matrix _ _ _ _ _
    _ = if transported row = value.2 ∧ transported column = value.2 then
          (state.block (labels.symm value.1)).matrix (basis.symm row) (basis.symm column)
        else 0 := by
      simp only [rowRead, columnRead, outcomes.symm.injective.eq_iff]
    _ = _ := ((ZMeasurement.branch_matrix transported value.2
      (((state.mapClassical labels).reindex basis).block value.1) row column).trans
        (congrArg (fun entry =>
          if transported row = value.2 ∧ transported column = value.2 then entry else 0)
            target)).symm

/-- The actual deterministic store writes commute with an exact relabeling diagram. -/
lemma coordinate_mapClassical_diagram {E F : Type} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (state : ExecutionState C R) (labels : C ≃ D) (results : E ≃ F)
    (first : C → E) (second : D → F)
    (commutes : ∀ value, results (first value) = second (labels value)) :
    (state.mapClassical first).mapClassical results =
      (state.mapClassical labels).mapClassical second := by
  rw [executionState_mapClassical_comp, executionState_mapClassical_comp]
  exact congrArg (state.mapClassical) (funext commutes)

/-- The same actual write diagram holds in the corresponding complete quantum coordinates. -/
lemma coordinate_transport_diagram {E F : Type} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (state : ExecutionState C R) (basis : R.Index ≃ S.Index)
    (labels : C ≃ D) (results : E ≃ F) (first : C → E) (second : D → F)
    (commutes : ∀ value, results (first value) = second (labels value)) :
    ((state.mapClassical first).mapClassical results).reindex basis =
      ((state.mapClassical labels).reindex basis).mapClassical second :=
  (congrArg (fun original => original.reindex basis)
    (coordinate_mapClassical_diagram state labels results first second commutes)).trans
      (coordinate_reindex_mapClassical (state.mapClassical labels) basis second).symm

end

end QuantumAlg.ExecutionState
