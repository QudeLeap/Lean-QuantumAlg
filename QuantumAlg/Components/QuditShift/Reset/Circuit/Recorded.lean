/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics

/-!
# Actual reset records with arbitrary surrounding classical grants

The existing reset executes only MZ, a structural read of that same cell,
and its actual native correction. Unused classical operations and services
do not change those instructions. Every complete original record and
external-reference entry remains in the exact output block equation.
-/

namespace QuantumAlg.QuditShift.Recorded

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

private instance recordedDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : Realizations gates oracles ctx.quantumLayout wire)

/-- The actual write and same-cell branch retain their original complete path. -/
def record {History : Type}
    (entry : Store ctx × (services.HiddenState × History))
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) :
    Store ctx × (services.HiddenState ×
      (History × (resetCircuit wire output realizations operations services false).Path)) :=
  (entry.1.write output (.finite outcome),
    (entry.2.1, (entry.2.2, (outcome, ⟨.finite outcome, ()⟩))))

/-- Actual execution keeps arbitrary Store overwrites, service history and Reference. -/
lemma execute
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (resetCircuit wire output realizations operations services false).execute
        environment Reference state =
      ((ExecutionState.measureZ state
        (fun basis : (Register.prod ctx.register Reference).Index => basis.1 wire)).applyUnitary
          fun entry =>
        UnitaryOperator.prodTensor (operator ctx.quantumLayout wire (-entry.2))
          (1 : UnitaryOperator Reference)).mapClassical
            (fun entry => record (operations := operations) wire output realizations
              entry.1 entry.2) := by
  have sequential := Circuit.execute_seq (environment := environment)
    (allowAllocation := false)
    (Circuit.measureZ (allowAllocation := false)
      (classicalOracles := services) (operations := operations)
      (gates := gates) (oracles := oracles) wire output)
    (Circuit.branch (.storage output.toCStorageRef) (fun value =>
      Circuit.unitary (allowAllocation := false) (realizations (-value.toFin)).circuit)) state
  refine sequential.trans ?_
  simp only [Circuit.execute_measureZ, Circuit.selectedUnitary_execute,
    ExecutionState.applyUnitary_mapClassical, Store.read_write_same,
    CShape.Value.toFin_finite, State.mapHistory,
    UnitaryCircuit.ExactRealization.matrix_eq,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  have readBack :
      (fun entry : (Store ctx × (services.HiddenState × History)) ×
          Fin (ctx.quantumLayout.wire wire).dimension =>
        (show Store ctx × (services.HiddenState ×
          (History × (resetCircuit wire output realizations operations services false).Path)) from
          (entry.1.1.write output (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, (entry.2,
              ⟨(entry.1.1.write output (.finite entry.2)).read
                (.storage output.toCStorageRef), ()⟩)))))) =
      (fun entry => record (operations := operations) wire output realizations
        entry.1 entry.2) := by
    funext entry
    exact congrArg
      (fun value : (CShape.finite (ctx.quantumLayout.wire wire).dimension).Value =>
        (show Store ctx × (services.HiddenState ×
          (History × (resetCircuit wire output realizations operations services false).Path)) from
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

/-- Every actual record has physical zero on this wire and retains its exact other entries. -/
lemma block_entry
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (resetCircuit wire output realizations operations services false).Path)))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index) :
    (((resetCircuit wire output realizations operations services false).execute
      environment Reference state).block result).matrix
        (left, refLeft) (right, refRight) =
      ∑ entry : Store ctx × (services.HiddenState × History), ∑ outcome,
        if record (operations := operations) wire output realizations entry outcome = result then
          if left wire = 0 ∧ right wire = 0 then
            (state.block entry).matrix (Function.update left wire outcome, refLeft)
              (Function.update right wire outcome, refRight)
          else 0
        else 0 := by
  rw [execute, ExecutionState.mapClassical_block_matrix]
  simp only [Matrix.sum_apply, ExecutionState.applyUnitary_block]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro entry _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : record (operations := operations) wire output realizations
      entry outcome = result
  · simp only [written, if_true]
    exact resetCircuitBranch_entry wire outcome (state.block entry) left right refLeft refRight
  · simp only [written, if_false]
    rfl

end

end QuantumAlg.QuditShift.Recorded
