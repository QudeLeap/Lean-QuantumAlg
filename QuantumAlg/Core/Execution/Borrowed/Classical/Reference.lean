/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Measurement.Reference
import all QuantumAlg.Core.Execution.Borrowed.Classical

/-!
# Classical inputs and their reference under local quantum execution

When no quantum wire is borrowed, every borrowed classical value still selects
its own full reference matrix. Actual local unitary steps and Z measurements
preserve each of these matrices, including correlations between the classical
input and the external reference [dW19, qcnotes.tex:5381,5405,5409]. The actual
measurement result is written to its writable cell before this observation.
Neither a singleton classical input nor an independent reference is required.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution

/-- With no borrowed quantum wires, each classical block retains its full reference matrix. -/
lemma observeBorrowed_noQuantum_entry {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (noQuantum : ctx.borrowedQuantumWires = []) {Reference : Register}
    {H : Type} [Fintype H] (state : State ctx Reference H)
    (value : ctx.borrowedClassicalShape.Value)
    (left right : ctx.borrowedQuantumLayout.Basis) (refLeft refRight : Reference.Index) :
    ((observeBorrowed Reference state).block value).matrix (left, refLeft) (right, refRight) =
      ∑ basis : ctx.register.Index,
        ((state.mapClassical fun label => label.1.readBorrowedClassical).block value).matrix
          (basis, refLeft) (basis, refRight) := by
  have empty : ctx.borrowedSelection = ∅ := by
    ext index
    simp [RuntimeCtx.mem_borrowedSelection, noQuantum]
  rw [observeBorrowed_block, RuntimeCtx.observeBorrowedWithReference_entry]
  exact sum_emptyComplement_diagonal ctx.quantumLayout ctx.borrowedSelection empty
    (ctx.borrowedBasisEquiv.symm left) (ctx.borrowedBasisEquiv.symm right)
    (fun a b =>
      ((state.mapClassical fun label => label.1.readBorrowedClassical).block value).matrix
        (a, refLeft) (b, refRight))

end Execution

namespace Circuit

variable {allowAllocation : Bool} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}

variable (environment : ExecutionModel.Environment
  (.quantum gates oracles operations classicalOracles))

open Execution

/-- A local unitary restores every borrowed classical value jointly with its reference. -/
lemma borrowedRestored_unitary_classicalReference {ctx : RuntimeCtx .quantum}
    (noQuantum : ctx.borrowedQuantumWires = []) {Reference : Register}
    {H : Type} [Fintype H] (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (state : State ctx Reference (classicalOracles.HiddenState × H)) :
    (Circuit.unitary (allowAllocation := allowAllocation) (operations := operations)
      (classicalOracles := classicalOracles) program).BorrowedRestored Reference state
      ((Circuit.unitary (allowAllocation := allowAllocation) (operations := operations)
        (classicalOracles := classicalOracles) program).execute environment Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_unitary]
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, refLeft⟩
  rcases column with ⟨right, refRight⟩
  rw [observeBorrowed_noQuantum_entry noQuantum,
    observeBorrowed_noQuantum_entry noQuantum]
  simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  rw [← ExecutionState.applyUnitary_mapClassical state
    (fun label : Store ctx × (classicalOracles.HiddenState × H) => label.1.readBorrowedClassical)
    (fun _ : ctx.borrowedClassicalShape.Value =>
      UnitaryOperator.prodTensor (program.matrix environment.quantum)
        (1 : UnitaryOperator Reference))]
  exact DensityOperator.localUnitary_reference_entry (program.matrix environment.quantum) _
    refLeft refRight

/-- Actual Z measurement preserves every borrowed classical-reference correlation. -/
lemma borrowedRestored_measureZ_classicalReference {ctx : RuntimeCtx .quantum}
    (noQuantum : ctx.borrowedQuantumWires = []) (item : ZReadout ctx)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (classicalOracles.HiddenState × H)) :
    (Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) item.wire
      item.output).BorrowedRestored Reference state
      ((Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) item.wire
        item.output).execute environment Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_measureZ]
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, refLeft⟩
  rcases column with ⟨right, refRight⟩
  rw [observeBorrowed_noQuantum_entry noQuantum,
    observeBorrowed_noQuantum_entry noQuantum]
  simp only [ExecutionState.executionState_mapClassical_comp,
    Function.comp_def, Store.readBorrowedClassical_write]
  apply Finset.sum_congr rfl
  intro basis _
  simp only [ExecutionState.mapClassical, Matrix.sum_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro label _
  by_cases same : label.readBorrowedClassical = value
  · simp [same, ZMeasurement.branch_matrix]
  · simp [same]

/-- A finite actual Z sequence preserves borrowed classical inputs jointly with their reference. -/
lemma borrowedRestored_measurementSequence_classicalReference {ctx : RuntimeCtx .quantum}
    (noQuantum : ctx.borrowedQuantumWires = []) (readouts : List (ZReadout ctx))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (classicalOracles.HiddenState × H)) :
    (measurementSequence (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) readouts).BorrowedRestored
      Reference state
      ((measurementSequence (allowAllocation := allowAllocation) (gates := gates)
        (oracles := oracles) (operations := operations)
        (classicalOracles := classicalOracles) readouts).execute environment
        Reference state) := by
  induction readouts generalizing H with
  | nil =>
      exact borrowedRestored_id (environment := environment) (allowAllocation := allowAllocation)
        (model := .quantum gates oracles operations classicalOracles)
        (ctx := ctx) (Reference := Reference) (H := H) state
  | cons head tail ih =>
      exact borrowedRestored_seq (environment := environment)
        (Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
          (operations := operations) (classicalOracles := classicalOracles) head.wire head.output)
        (measurementSequence (allowAllocation := allowAllocation) (gates := gates)
          (oracles := oracles) (operations := operations)
          (classicalOracles := classicalOracles) tail) state
        (borrowedRestored_measureZ_classicalReference
          (environment := environment) (allowAllocation := allowAllocation)
          (gates := gates) (oracles := oracles) (operations := operations)
          (classicalOracles := classicalOracles)
          noQuantum head state) (ih _)

end Circuit

end

end QuantumAlg
