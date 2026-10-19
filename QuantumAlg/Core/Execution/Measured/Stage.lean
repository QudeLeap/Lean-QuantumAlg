/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Measure.Instrument

/-!
# Complete stored blocks of literal measurement and feedback stages

A literal Z instruction writes its actual outcome before the subsequent
native program is selected from that same cell [dW19, qcnotes.tex:5409,5420].
Each final store collects every original block that reaches it. In particular,
an overwritten cell need not start in a fixed value or be independent of the
quantum input. All physical systems and external-reference coordinates remain
in each unnormalized branch matrix. These are equations for the existing
interpreter, with no extra execution or state representation.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- A literal Z write sums all original blocks reaching its actual complete final store. -/
lemma measureZ_store_matrix
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (ExecutionState.filterClassical
      ((Circuit.measureZ (allowAllocation := false) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) wire output).execute
          environment Reference state) (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : Fin (ctx.quantumLayout.wire wire).dimension,
          if original.1.write output (.finite outcome) = stored then
            (ZMeasurement.branch (R := ctx.register.prod Reference)
              (fun basis => basis.1 wire) outcome (state.block original)).matrix
          else 0 := by
  ext left right
  rw [ExecutionState.filterClassical_matrix_weighted, Circuit.execute_measureZ]
  refine (@ExecutionState.weightedMatrixEntry_mapClassical
    ((Store ctx × (services.HiddenState × History)) ×
      Fin (ctx.quantumLayout.wire wire).dimension)
    (Store ctx × (services.HiddenState ×
      (History × Fin (ctx.quantumLayout.wire wire).dimension))) _ _ _ _
    (ExecutionState.measureZ state (fun basis => basis.1 wire))
    (fun entry => (entry.1.1.write output (.finite entry.2),
      (entry.1.2.1, (entry.1.2.2, entry.2))))
    (fun entry => if entry.1 = stored then (1 : ℂ) else 0) left right).trans ?_
  simp only [ExecutionState.weightedMatrixEntry, Fintype.sum_prod_type,
    ExecutionState.measureZ_block, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    ite_mul, one_mul, zero_mul]

/-- The actual written value selects its native feedback on every contributing original block. -/
lemma measureZ_selected_store_matrix
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (program : CShape.Value (.finite (ctx.quantumLayout.wire wire).dimension) →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (ExecutionState.filterClassical
      ((Circuit.seq
        (.measureZ (allowAllocation := false) (gates := gates) (oracles := oracles)
          (operations := operations) (classicalOracles := services) wire output)
        (.branch (.storage output.toCStorageRef) (fun value => .unitary (program value)))).execute
          environment Reference state) (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : Fin (ctx.quantumLayout.wire wire).dimension,
          if original.1.write output (.finite outcome) = stored then
            (DensityOperator.applyUnitary
              (UnitaryOperator.prodTensor ((program (.finite outcome)).matrix environment.quantum)
                (1 : UnitaryOperator Reference))
              (ZMeasurement.branch (R := ctx.register.prod Reference)
                (fun basis => basis.1 wire) outcome (state.block original))).matrix
          else 0 := by
  let measured : State ctx Reference
      (services.HiddenState × (History × Fin (ctx.quantumLayout.wire wire).dimension)) :=
    (Circuit.measureZ (allowAllocation := false) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services) wire output).execute
        environment Reference state
  have composed := congrArg DensityOperator.matrix
    (seq_store_marginal
      (.measureZ (allowAllocation := false) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) wire output)
      (.branch (.storage output.toCStorageRef) (fun value => .unitary (program value)))
      environment state stored)
  have selected := selectedUnitary_store_matrix (allowAllocation := false)
    (operations := operations) (classicalOracles := services)
    (.storage output.toCStorageRef) program environment measured stored
  refine composed.trans (selected.trans ?_)
  dsimp only [measured]
  rw [DensityOperator.applyUnitary_matrix]
  let feedback := UnitaryOperator.prodTensor
    ((program (stored.read (.storage output.toCStorageRef))).matrix environment.quantum)
      (1 : UnitaryOperator Reference)
  have pushed := congrArg
    (fun matrix : HilbertOperator (ctx.register.prod Reference) =>
      (feedback : HilbertOperator (ctx.register.prod Reference)) * matrix *
        (feedback : HilbertOperator (ctx.register.prod Reference)).conjTranspose)
    (measureZ_store_matrix (gates := gates) (oracles := oracles)
      (operations := operations) (services := services) wire output environment state stored)
  refine pushed.trans ?_
  dsimp only [feedback]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro original _
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : original.1.write output (.finite outcome) = stored
  · simp only [if_pos written]
    have actual : program (stored.read (.storage output.toCStorageRef)) =
        program (.finite outcome) := by
      rw [← written, Store.read_write_same]
    rw [actual]
    rfl
  · simp only [if_neg written, Matrix.mul_zero, Matrix.zero_mul]

/-- The same three real instructions have the complete retained-bank Kraus action.

The sum retains the original classical/service/history labels and all outcomes
that actually write the final store. The arbitrary reference is acted on only
by its identity, and no measured physical quantum system is removed.
-/
lemma unitary_measureZ_selected_store_matrix
    (preparation : UnitaryCircuit gates oracles ctx.quantumLayout)
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (program : CShape.Value (.finite (ctx.quantumLayout.wire wire).dimension) →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (ExecutionState.filterClassical
      ((Circuit.seq
        (.unitary (allowAllocation := false) (operations := operations)
          (classicalOracles := services) preparation)
        (.seq (.measureZ wire output)
          (.branch (.storage output.toCStorageRef)
            (fun value => .unitary (program value))))).execute
          environment Reference state) (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : Fin (ctx.quantumLayout.wire wire).dimension,
          if original.1.write output (.finite outcome) = stored then
            let operator : HilbertOperator (ctx.register.prod Reference) :=
              (UnitaryOperator.prodTensor ((program (.finite outcome)).matrix environment.quantum)
                (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference)) *
                ZMeasurement.projector (R := ctx.register.prod Reference)
                  (fun basis => basis.1 wire) outcome *
                (UnitaryOperator.prodTensor (preparation.matrix environment.quantum)
                  (1 : UnitaryOperator Reference) :
                  HilbertOperator (ctx.register.prod Reference))
            operator * (state.block original).matrix * operator.conjTranspose
          else 0 := by
  let afterPrefix : State ctx Reference (services.HiddenState × (History × Unit)) :=
    (Circuit.unitary (allowAllocation := false) (operations := operations)
      (classicalOracles := services) preparation).execute environment Reference state
  have composed := congrArg DensityOperator.matrix
    (seq_store_marginal
      (.unitary (allowAllocation := false) (operations := operations)
        (classicalOracles := services) preparation)
      (.seq (.measureZ wire output)
        (.branch (.storage output.toCStorageRef) (fun value => .unitary (program value))))
      environment state stored)
  have measured := measureZ_selected_store_matrix (operations := operations) (services := services)
    wire output program environment afterPrefix stored
  refine composed.trans (measured.trans ?_)
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro originalStore _
  apply Finset.sum_congr rfl
  intro hidden _
  apply Finset.sum_congr rfl
  intro history _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : originalStore.write output (.finite outcome) = stored
  · have unit : (default : Unit) = () := Subsingleton.elim _ _
    have acted := Circuit.execute_unitary_block_matrix (allowAllocation := false)
      (operations := operations) (services := services) (quantumEnvironment := environment)
      state preparation originalStore hidden history
    simp only [if_pos written, DensityOperator.applyUnitary_matrix, ZMeasurement.branch,
      afterPrefix, unit, acted, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp only [if_neg written]

end

end QuantumAlg.Circuit
