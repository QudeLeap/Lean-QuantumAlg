/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Full matrix entries of actual Z writes and classical feed-forward

The existing measurement sequence writes each real Z outcome to its
classical result cell. The following existing branch reads the resulting
store and executes its selected unitary program. The equation retains
every final store and both arbitrary local and reference coordinates;
it therefore keeps the relative phases needed by measured arithmetic
[dW19, qcnotes.tex:5405,5409,5420].

No result is supplied independently of execution. The actual writes,
selection and unitary all come from the same composed circuit.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

namespace ExecutionState

/-- Selecting classical blocks is exactly the corresponding indicator-weighted full entry. -/
lemma filterClassical_matrix_weighted {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (predicate : C → Prop) [DecidablePred predicate]
    (left right : R.Index) :
    (state.filterClassical predicate).quantumMarginal.matrix left right =
      weightedMatrixEntry state (fun value => if predicate value then 1 else 0) left right := by
  change (∑ value : C, (if predicate value then state.block value else
    DensityOperator.zero R).matrix) left right = _
  simp only [weightedMatrixEntry, Matrix.sum_apply, apply_ite DensityOperator.matrix,
    Matrix.ite_apply, DensityOperator.zero_matrix, Matrix.zero_apply, ite_mul, one_mul, zero_mul]

end ExecutionState

namespace Circuit

variable {allowAllocation : Bool}

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}

open Execution

/-- Each final store has the full quantum block selected by its actual ordered Z writes. -/
lemma measurementSequence_store_matrix_entry {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx))
    (environment : (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (stored : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical ((measurementSequence (allowAllocation := allowAllocation)
      (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts).execute
      environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if measurementLabelsAgree readouts left right then
        ExecutionState.weightedMatrixEntry state (fun original =>
          if writeMeasurementPath (allowAllocation := allowAllocation) (gates := gates) (oracles :=
            oracles)
            (operations := operations) (classicalOracles := classicalOracles)
            readouts original.1
            (measurementBasisPath (allowAllocation := allowAllocation) (gates := gates) (oracles :=
              oracles)
              (operations := operations) (classicalOracles := classicalOracles)
              readouts left) =
            stored then 1 else 0) (left, leftRef) (right, rightRef)
      else 0 := by
  rw [ExecutionState.filterClassical_matrix_weighted,
    measurementSequence_weightedMatrixEntry]

/-- Actual stored results select the later gates on every full local-reference matrix entry. -/
lemma measuredSelectedUnitary_store_entry {ctx : RuntimeCtx .quantum} {shape : CShape}
    (readouts : List (ZReadout ctx)) (input : CInputRef ctx shape)
    (program : shape.Value → UnitaryCircuit gates oracles ctx.quantumLayout)
    (environment : (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (stored : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((Circuit.seq (measurementSequence (allowAllocation := allowAllocation) (gates := gates)
        (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) readouts)
        (.branch (allowAllocation := allowAllocation) input (fun value => .unitary
          (operations := operations) (classicalOracles := classicalOracles)
          (program value)))).execute
          environment Reference state) (fun entry => entry.1 = stored)).quantumMarginal.matrix
            (left, leftRef) (right, rightRef) =
      ∑ column : ctx.register.Index, (∑ row : ctx.register.Index,
        ((program (stored.read input)).matrix environment.quantum) left row *
          (if measurementLabelsAgree readouts row column then
            ExecutionState.weightedMatrixEntry state (fun original =>
              if writeMeasurementPath (allowAllocation := allowAllocation) (gates := gates) (oracles
                := oracles)
                (operations := operations) (classicalOracles := classicalOracles)
                readouts original.1
                (measurementBasisPath (allowAllocation := allowAllocation) (gates := gates) (oracles
                  := oracles)
                  (operations := operations) (classicalOracles := classicalOracles)
                  readouts row) =
                stored then 1 else 0) (row, leftRef) (column, rightRef)
          else 0)) *
            star (((program (stored.read input)).matrix environment.quantum) right column) := by
  have composed := congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef))
    (seq_store_marginal (measurementSequence (allowAllocation := allowAllocation) (gates := gates)
      (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) readouts)
      (.branch (allowAllocation := allowAllocation) input (fun value => .unitary
        (operations := operations) (classicalOracles := classicalOracles)
        (program value))) environment state stored)
  have selected := congrArg
    (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      matrix (left, leftRef) (right, rightRef))
    (selectedUnitary_store_matrix (allowAllocation := allowAllocation) (operations := operations)
      (classicalOracles := classicalOracles) input program environment
      ((measurementSequence (allowAllocation := allowAllocation) (gates := gates) (oracles :=
        oracles)
        (operations := operations) (classicalOracles := classicalOracles) readouts).execute
        environment Reference state) stored)
  refine composed.trans (selected.trans ?_)
  rw [DensityOperator.localUnitary_block]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro column _
  apply congrArg (fun entry =>
    entry * star (((program (stored.read input)).matrix environment.quantum) right column))
  apply Finset.sum_congr rfl
  intro row _
  apply congrArg (fun entry =>
    ((program (stored.read input)).matrix environment.quantum) left row * entry)
  exact measurementSequence_store_matrix_entry (allowAllocation := allowAllocation) (gates := gates)
    (oracles := oracles)
    (operations := operations) (classicalOracles := classicalOracles)
    readouts environment state stored row column leftRef rightRef

end Circuit

end

end QuantumAlg
