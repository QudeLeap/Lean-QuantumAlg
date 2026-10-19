/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit
import all QuantumAlg.Components.QuditShift.Reset
import all QuantumAlg.Core.Execution.Selected.Store

/-!
# Full state of the actual stored-result reset circuit

The actual Z instruction writes its outcome into the supplied finite cell.
The subsequent branch reads that cell and applies its negative shift beside
the identity on an arbitrary reference. Every old store and history remains
in the exact finite sum, including collisions caused by overwriting the cell.
The final wire is zero and the other systems retain their original joint
marginal. No separability, normalization, or initial cell value is assumed.
-/

namespace QuantumAlg.QuditShift

noncomputable section

variable {services : ClassicalOracleModel}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private instance semanticsDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {gates : GateModel} {oracles : OracleModel}
variable {environment : (ExecutionModel.quantum gates oracles .empty services).Environment}
variable {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
  (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
  (realizations : Realizations gates oracles ctx.quantumLayout wire)

/-- The actual record writes and then reads the same measured finite value. -/
def resetCircuitRecord {allowAllocation : Bool} {History : Type}
    (entry : Store ctx ×
      ((ExecutionModel.quantum gates oracles .empty services).HiddenState × History))
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) :
    Store ctx × ((ExecutionModel.quantum gates oracles .empty services).HiddenState ×
      (History × (resetCircuit (allowAllocation := allowAllocation) (services := services) wire
          output realizations).Path)) :=
  (entry.1.write output (.finite outcome),
    (entry.2.1, (entry.2.2, (outcome, ⟨.finite outcome, ()⟩))))

/-- The complete interpreter state retains the actual store, history, result and reference. -/
lemma resetCircuit_execute {allowAllocation : Bool} {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History)) :
    (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations).execute environment Reference state =
      ((ExecutionState.measureZ state
        (fun basis : (Register.prod ctx.register Reference).Index => basis.1 wire)).applyUnitary
          fun entry =>
        UnitaryOperator.prodTensor (operator ctx.quantumLayout wire (-entry.2))
          (1 : UnitaryOperator Reference)).mapClassical
            (fun entry =>
              resetCircuitRecord (allowAllocation := allowAllocation) (services := services)
                wire output realizations entry.1 entry.2) := by
  have sequential := Circuit.execute_seq (environment := environment)
    (allowAllocation := allowAllocation)
    (Circuit.measureZ (allowAllocation := allowAllocation)
      (classicalOracles := services) (gates := gates) (oracles := oracles) wire output)
    (Circuit.branch (.storage output.toCStorageRef) (fun value =>
      Circuit.unitary (allowAllocation := allowAllocation)
        (realizations (-value.toFin)).circuit)) state
  refine sequential.trans ?_
  simp only [Circuit.execute_measureZ, Circuit.selectedUnitary_execute,
    ExecutionState.applyUnitary_mapClassical,
    Store.read_write_same, CShape.Value.toFin_finite, State.mapHistory,
    UnitaryCircuit.ExactRealization.matrix_eq,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  have readBack :
      (fun entry : (Store ctx × ((ExecutionModel.quantum gates oracles .empty services).HiddenState
        × History)) ×
          Fin (ctx.quantumLayout.wire wire).dimension =>
        (show Store ctx × ((ExecutionModel.quantum gates oracles .empty services).HiddenState ×
            (History × (resetCircuit (allowAllocation := allowAllocation) (services := services)
                wire output realizations).Path)) from
          (entry.1.1.write output (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, (entry.2,
            ⟨(entry.1.1.write output (.finite entry.2)).read
              (.storage output.toCStorageRef), ()⟩)))))) =
        (fun entry =>
          resetCircuitRecord (allowAllocation := allowAllocation) (services := services)
            wire output realizations entry.1 entry.2) := by
    funext entry
    exact congrArg
      (fun value : (CShape.finite (ctx.quantumLayout.wire wire).dimension).Value =>
        (show Store ctx × ((ExecutionModel.quantum gates oracles .empty services).HiddenState ×
            (History × (resetCircuit (allowAllocation := allowAllocation) (services := services)
                wire output realizations).Path)) from
          (entry.1.1.write output (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, (entry.2, ⟨value, ()⟩))))))
        (Store.read_write_same entry.1.1 output (.finite entry.2))
  have updated := congrArg (fun update =>
    ((ExecutionState.measureZ state
      (fun basis : (Register.prod ctx.register Reference).Index => basis.1 wire)).applyUnitary
        fun entry => UnitaryOperator.prodTensor
          (operator ctx.quantumLayout wire (-entry.2))
          (1 : UnitaryOperator Reference)).mapClassical update) readBack
  refine Eq.trans ?_ updated
  congr 1
  exact Subsingleton.elim _ _

private lemma operator_reference_permutation {systemCount : Nat}
    (layout : QuantumLayout systemCount) (selected : Fin systemCount)
    (amount : Fin (layout.wire selected).dimension) (Reference : Register) :
    UnitaryOperator.prodTensor (operator layout selected amount)
      (1 : UnitaryOperator Reference) =
      UnitaryOperator.ofPerm ((labelShift layout selected amount).symm.prodCongr
        (Equiv.refl Reference.Index)) := by
  apply Subtype.ext
  ext left right
  rw [UnitaryOperator.prodTensor_apply]
  change (Equiv.Perm.permMatrix ℂ (labelShift layout selected amount).symm) left.1 right.1 *
    (1 : Matrix Reference.Index Reference.Index ℂ) left.2 right.2 =
      (Equiv.Perm.permMatrix ℂ ((labelShift layout selected amount).symm.prodCongr
        (Equiv.refl Reference.Index))) left right
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Matrix.one_apply, Equiv.prodCongr_apply, Prod.ext_iff, ite_and]
  split_ifs <;> simp_all

/-- A single actual measured branch resets this wire and retains every reference matrix entry. -/
lemma resetCircuitBranch_entry {Reference : Register}
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension)
    (density : DensityOperator (Register.prod ctx.register Reference))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (operator ctx.quantumLayout wire (-outcome))
        (1 : UnitaryOperator Reference))
      (ZMeasurement.branch (R := Register.prod ctx.register Reference)
        (fun basis => basis.1 wire) outcome density)).matrix
        (left, refLeft) (right, refRight) =
      if left wire = 0 ∧ right wire = 0 then
        density.matrix (Function.update left wire outcome, refLeft)
          (Function.update right wire outcome, refRight)
      else 0 := by
  rw [operator_reference_permutation, ZReset.permutationDensityEntry]
  change (ZMeasurement.branch (R := Register.prod ctx.register Reference)
    (fun basis => basis.1 wire) outcome density).matrix
    (Function.update left wire (left wire - -outcome), refLeft)
    (Function.update right wire (right wire - -outcome), refRight) = _
  rw [ZMeasurement.branch_matrix]
  simp only [Function.update_self, sub_neg_eq_add, ZReset.shiftedLabelEqOutcome]
  by_cases hl : left wire = 0 <;> by_cases hr : right wire = 0 <;> simp [hl, hr]

/-- Exact actual output blocks sum all old stores and histories that write that complete record. -/
lemma resetCircuit_block_entry {allowAllocation : Bool} {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History))
    (result : Store ctx × ((ExecutionModel.quantum gates oracles .empty services).HiddenState ×
      (History × (resetCircuit (allowAllocation := allowAllocation) (services := services) wire
          output realizations).Path)))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index) :
    (((resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations).execute environment Reference state).block
      result).matrix
        (left, refLeft) (right, refRight) =
      ∑ entry : Store ctx ×
          ((ExecutionModel.quantum gates oracles .empty services).HiddenState × History), ∑ outcome,
        if resetCircuitRecord (allowAllocation := allowAllocation) (services := services) wire
            output realizations entry outcome =
          result then
          if left wire = 0 ∧ right wire = 0 then
            (state.block entry).matrix (Function.update left wire outcome, refLeft)
              (Function.update right wire outcome, refRight)
          else 0
        else 0 := by
  rw [resetCircuit_execute (allowAllocation := allowAllocation),
      ExecutionState.mapClassical_block_matrix]
  simp only [Matrix.sum_apply, ExecutionState.applyUnitary_block]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro entry _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : resetCircuitRecord (allowAllocation := allowAllocation) (services := services)
      wire output realizations entry outcome = result
  · simp only [written, if_true]
    exact resetCircuitBranch_entry wire outcome (state.block entry) left right refLeft refRight
  · simp only [written, if_false]
    rfl

/-- Summing actual output records retains the original joint marginal of all other systems. -/
lemma resetCircuit_quantum_entry {allowAllocation : Bool} {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History))
    (left right : ctx.quantumLayout.Basis)
    (refLeft refRight : Reference.Index) :
    ((resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations).execute environment Reference
      state).quantumMarginal.matrix
        (left, refLeft) (right, refRight) =
      if left wire = 0 ∧ right wire = 0 then
        ∑ entry : Store ctx ×
            ((ExecutionModel.quantum gates oracles .empty services).HiddenState × History), ∑
              outcome,
          (state.block entry).matrix (Function.update left wire outcome, refLeft)
            (Function.update right wire outcome, refRight)
      else 0 := by
  rw [resetCircuit_execute (allowAllocation := allowAllocation),
      ExecutionState.mapClassical_quantumMarginal]
  change (∑ entry : (Store ctx × ((ExecutionModel.quantum gates oracles .empty
    services).HiddenState × History)) ×
      Fin (ctx.quantumLayout.wire wire).dimension,
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (operator ctx.quantumLayout wire (-entry.2))
        (1 : UnitaryOperator Reference))
      (ZMeasurement.branch (R := Register.prod ctx.register Reference)
        (fun basis => basis.1 wire) entry.2 (state.block entry.1))).matrix)
        (left, refLeft) (right, refRight) = _
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, resetCircuitBranch_entry]
  by_cases zero : left wire = 0 ∧ right wire = 0 <;> simp [zero]

/-- The actual measured correction preserves the complete execution mass. -/
lemma resetCircuit_mass {allowAllocation : Bool} {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles .empty
      services).HiddenState × History)) :
    ((resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations).execute environment Reference state).mass =
      state.mass :=
  Circuit.execute_mass _ environment _ _

end

end QuantumAlg.QuditShift
