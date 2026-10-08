/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics

/-!
# Full state of direct measured basis preparation

The actual measured outcome selects one correction to the target basis value.
Every previous store, history and external-reference matrix entry remains in
the complete weighted state. The result cell need not be fresh, and impossible
branches remain zero. No intermediate reset or second reload is executed.
-/

namespace QuantumAlg.QuditShift

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private instance directBasisDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {gates : GateModel} {oracles : OracleModel}
variable {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
  (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
  (realizations : Realizations gates oracles ctx.quantumLayout wire)
  (value : Fin (ctx.quantumLayout.wire wire).dimension)

/-- The actual record writes and then reads the same measured finite value. -/
def resetWireToBasisRecord {History : Type}
    (entry : Store ctx ×
      ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) :
    Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState ×
      (History × (resetWireToBasis wire realizations output value).Path)) :=
  (entry.1.write output (.finite outcome),
    (entry.2.1, (entry.2.2, (outcome, ⟨.finite outcome, ()⟩))))

/-- The complete interpreter state retains the actual store, history, result and reference. -/
theorem resetWireToBasis_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History)) :
    (resetWireToBasis wire realizations output value).execute Reference state =
      ((ExecutionState.measureZ state
        (fun basis : (Register.prod ctx.register Reference).Index => basis.1 wire)).applyUnitary
          fun entry =>
        UnitaryOperator.prodTensor (operator ctx.quantumLayout wire (value - entry.2))
          (1 : UnitaryOperator Reference)).mapClassical
            (fun entry =>
              resetWireToBasisRecord wire output realizations value entry.1 entry.2) := by
  have sequential := Circuit.execute_seq
    (Circuit.measureZ (gates := gates) (oracles := oracles) wire output)
    (Circuit.branch (.storage output.toCStorageRef) (fun outcome =>
      Circuit.unitary (realizations (value - outcome.toFin)).circuit)) state
  refine sequential.trans ?_
  simp only [Circuit.execute_measureZ, Circuit.selectedUnitary_execute,
    ExecutionState.applyUnitary_mapClassical,
    Store.read_write_same, CShape.Value.toFin_finite, State.mapHistory,
    UnitaryCircuit.ExactRealization.matrix_eq,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  have readBack :
      (fun entry : (Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState × History)) ×
          Fin (ctx.quantumLayout.wire wire).dimension =>
        (show Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState ×
            (History × (resetWireToBasis wire realizations output value).Path)) from
          (entry.1.1.write output (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, (entry.2,
            ⟨(entry.1.1.write output (.finite entry.2)).read
              (.storage output.toCStorageRef), ()⟩)))))) =
        (fun entry =>
              resetWireToBasisRecord wire output realizations value entry.1 entry.2) := by
    funext entry
    exact congrArg
      (fun storedValue : (CShape.finite (ctx.quantumLayout.wire wire).dimension).Value =>
        (show Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState ×
            (History × (resetWireToBasis wire realizations output value).Path)) from
          (entry.1.1.write output (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, (entry.2, ⟨storedValue, ()⟩))))))
        (Store.read_write_same entry.1.1 output (.finite entry.2))
  have updated := congrArg (fun update =>
    ((ExecutionState.measureZ state
      (fun basis : (Register.prod ctx.register Reference).Index => basis.1 wire)).applyUnitary
        fun entry => UnitaryOperator.prodTensor
          (operator ctx.quantumLayout wire (value - entry.2))
          (1 : UnitaryOperator Reference)).mapClassical update) readBack
  refine Eq.trans ?_ updated
  congr 1
  exact Subsingleton.elim _ _

/-- One measured branch directly prepares the target with its full conditional reference state. -/
theorem resetWireToBasisBranch_entry {Reference : Register}
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension)
    (density : DensityOperator (Register.prod ctx.register Reference))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (operator ctx.quantumLayout wire (value - outcome))
        (1 : UnitaryOperator Reference))
      (ZMeasurement.branch (R := Register.prod ctx.register Reference)
        (fun basis => basis.1 wire) outcome density)).matrix
        (left, refLeft) (right, refRight) =
      if left wire = value ∧ right wire = value then
        density.matrix (Function.update left wire outcome, refLeft)
          (Function.update right wire outcome, refRight)
      else 0 := by
  rw [operator_reference_permutation, ZReset.permutationDensityEntry]
  change (ZMeasurement.branch (R := Register.prod ctx.register Reference)
    (fun basis => basis.1 wire) outcome density).matrix
    (Function.update left wire (left wire - (value - outcome)), refLeft)
    (Function.update right wire (right wire - (value - outcome)), refRight) = _
  rw [ZMeasurement.branch_matrix]
  have hit (coordinate : Fin (ctx.quantumLayout.wire wire).dimension) :
      coordinate - (value - outcome) = outcome ↔ coordinate = value := by
    rw [sub_eq_iff_eq_add, add_comm outcome, sub_add_cancel]
  simp only [Function.update_self, hit]
  by_cases hl : left wire = value <;> by_cases hr : right wire = value <;> simp [hl, hr]

/-- Actual blocks sum every old record and outcome that produces this complete final record. -/
theorem resetWireToBasis_block_entry {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (result : Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState ×
      (History × (resetWireToBasis wire realizations output value).Path)))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index) :
    (((resetWireToBasis wire realizations output value).execute Reference state).block
      result).matrix
        (left, refLeft) (right, refRight) =
      ∑ entry : Store ctx ×
          ((ExecutionModel.quantum gates oracles).HiddenState × History), ∑ outcome,
        if resetWireToBasisRecord wire output realizations value entry outcome = result then
          if left wire = value ∧ right wire = value then
            (state.block entry).matrix (Function.update left wire outcome, refLeft)
              (Function.update right wire outcome, refRight)
          else 0
        else 0 := by
  rw [resetWireToBasis_execute, ExecutionState.mapClassical_block_matrix]
  simp only [Matrix.sum_apply, ExecutionState.applyUnitary_block]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro entry _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : resetWireToBasisRecord wire output realizations value entry outcome = result
  · simp only [written, if_true]
    exact resetWireToBasisBranch_entry wire value outcome (state.block entry) left right
      refLeft refRight
  · simp only [written, if_false]
    rfl

end

end QuantumAlg.QuditShift
