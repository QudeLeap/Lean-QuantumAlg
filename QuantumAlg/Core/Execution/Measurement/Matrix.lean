/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Measure.Instrument

/-!
# Full quantum matrix entries after actual Z writes

Unlike a diagonal probability observation, these scalar sums retain two
arbitrary quantum coordinates. Actual Z measurement suppresses exactly
the entries whose measured values disagree; every unmeasured coordinate
and every external-reference entry is retained. The weight follows the
same actual stored outcome and finite execution path
[dW19, qcnotes.tex:5409,5420].

These are observations of the existing state and interpreter, not a new
state carrier, measurement primitive or executor.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

namespace ExecutionState

/-- An arbitrary full quantum matrix entry, weighted only by the actual classical block. -/
def weightedMatrixEntry {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (weight : C → ℂ) (left right : R.Index) : ℂ :=
  ∑ value : C, weight value * (state.block value).matrix left right

/-- Actual classical remapping transports the block weight without changing quantum coordinates. -/
theorem weightedMatrixEntry_mapClassical {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {R : Register} (state : ExecutionState C R) (update : C → D)
    (weight : D → ℂ) (left right : R.Index) :
    weightedMatrixEntry (state.mapClassical update) weight left right =
      weightedMatrixEntry state (fun value => weight (update value)) left right := by
  unfold weightedMatrixEntry
  change (∑ output : D, weight output *
    (∑ value : C, if update value = output then (state.block value).matrix else 0) left right) = _
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Z measurement preserves exactly the entries with equal measured values on both coordinates. -/
theorem weightedMatrixEntry_measureZ {C Outcome : Type} [Fintype C] [Fintype Outcome]
    [DecidableEq Outcome] {R : Register} (state : ExecutionState C R)
    (readout : R.Index → Outcome)
    (weight : C × Outcome → ℂ) (left right : R.Index) :
    weightedMatrixEntry (state.measureZ readout) weight left right =
      if readout left = readout right then
        weightedMatrixEntry state (fun value => weight (value, readout left)) left right
      else 0 := by
  simp only [weightedMatrixEntry, Fintype.sum_prod_type, measureZ_block,
    ZMeasurement.branch_matrix, mul_ite, mul_zero]
  by_cases same : readout left = readout right
  · rw [if_pos same]
    apply Finset.sum_congr rfl
    intro value _
    have condition (outcome : Outcome) :
        (readout left = outcome ∧ readout right = outcome) ↔ outcome = readout left := by
      rw [← same]
      simp only [and_self, eq_comm]
    simp only [condition, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg same]
    apply Finset.sum_eq_zero
    intro value _
    apply Finset.sum_eq_zero
    intro outcome _
    have different : ¬(readout left = outcome ∧ readout right = outcome) := by
      rintro ⟨first, second⟩
      exact same (first.trans second.symm)
    rw [if_neg different]

end ExecutionState

namespace Circuit

open Execution

/-- Two complete labels agree on every actually measured physical position. -/
def measurementLabelsAgree {ctx : RuntimeCtx .quantum} :
    List (ZReadout ctx) → ctx.register.Index → ctx.register.Index → Prop
  | [], _, _ => True
  | head :: tail, left, right =>
      left head.wire = right head.wire ∧ measurementLabelsAgree tail left right

/-- The actual Z sequence retains every unmeasured matrix entry and its actual classical writes. -/
theorem measurementSequence_weightedMatrixEntry {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (weight : Store ctx × (History × (measurementSequence readouts).Path) → ℂ)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry
        ((measurementSequence readouts).execute Reference state) weight
        (left, leftRef) (right, rightRef) =
      if measurementLabelsAgree readouts left right then
        ExecutionState.weightedMatrixEntry state
          (fun value => weight
            (writeMeasurementPath readouts value.1 (measurementBasisPath readouts left),
              (value.2, measurementBasisPath readouts left))) (left, leftRef) (right, rightRef)
      else 0 := by
  induction readouts generalizing History with
  | nil =>
      simp only [measurementSequence, execute_id, State.skip, State.mapHistory,
        ExecutionState.weightedMatrixEntry_mapClassical, measurementLabelsAgree,
        writeMeasurementPath, measurementBasisPath]
      exact (if_pos trivial).symm
  | cons head tail inductionHypothesis =>
      change ExecutionState.weightedMatrixEntry
        ((Circuit.seq (.measureZ head.wire head.output)
          (measurementSequence tail)).execute Reference state) weight _ _ = _
      rw [execute_seq]
      simp only [State.mapHistory, ExecutionState.weightedMatrixEntry_mapClassical]
      rw [inductionHypothesis]
      by_cases tailAgrees : measurementLabelsAgree tail left right
      · rw [if_pos tailAgrees, execute_measureZ]
        simp only [State.measureZ, ExecutionState.weightedMatrixEntry_mapClassical]
        rw [ExecutionState.weightedMatrixEntry_measureZ]
        simp only [measurementLabelsAgree, tailAgrees, and_true,
          writeMeasurementPath, measurementBasisPath]
      · simp only [measurementLabelsAgree, tailAgrees, and_false, if_false]

end Circuit

end

end QuantumAlg
