/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Measure.Instrument

/-!
# Untouched references under actual sequential Z measurements

Summing all outcomes of a local computational-basis measurement preserves
every matrix entry of the untouched reference. The real classical write and
finite path are retained before this observation; no prescribed outcome is
substituted for the one produced by the interpreter.

The proof uses the complete local-projector sum [dW19, qcnotes.tex:5409,5420]
and partial trace [dW19, qcnotes.tex:6827]. Reference inputs may be mixed or
correlated with any local system. The empty measurement sequence has the
same preservation law without a positive-width premise.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

/-- Summing a measured local coordinate preserves every untouched reference entry. -/
lemma measureZ_reference_entry {count : Nat} (layout : QuantumLayout count)
    (wire : Fin count) {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod layout.register Reference))
    (refLeft refRight : Reference.Index) :
    (∑ basis : layout.Basis,
      (state.measureZ (fun value => value.1 wire)).quantumMarginal.matrix
        (basis, refLeft) (basis, refRight)) =
      ∑ basis : layout.Basis,
        state.quantumMarginal.matrix (basis, refLeft) (basis, refRight) := by
  change (∑ basis : layout.Basis,
    (∑ result : C × Fin (layout.wire wire).dimension,
      (ZMeasurement.branch (R := Register.prod layout.register Reference)
        (fun value => value.1 wire) result.2 (state.block result.1)).matrix)
          (basis, refLeft) (basis, refRight)) =
    ∑ basis : layout.Basis, (∑ value : C, (state.block value).matrix)
      (basis, refLeft) (basis, refRight)
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, ZMeasurement.branch_matrix,
    and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end ExecutionState

namespace Circuit

variable {allowAllocation : Bool} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}

open Execution

variable (environment : ExecutionModel.Environment
  (.quantum gates oracles operations classicalOracles))

/-- Actual Z execution and its Store write leave the external reference unchanged. -/
lemma measurementStep_reference_entry {ctx : RuntimeCtx .quantum}
    (item : ZReadout ctx) {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (classicalOracles.HiddenState × H))
    (refLeft refRight : Reference.Index) :
    (∑ basis : ctx.register.Index,
      ((Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) item.wire
        item.output).execute environment Reference state).quantumMarginal.matrix
        (basis, refLeft) (basis, refRight)) =
      ∑ basis : ctx.register.Index,
        state.quantumMarginal.matrix (basis, refLeft) (basis, refRight) := by
  rw [execute_measureZ]
  simp only [ExecutionState.mapClassical_quantumMarginal]
  exact ExecutionState.measureZ_reference_entry ctx.quantumLayout item.wire state refLeft refRight

/-- A finite sequence preserves the same reference in its one actual complete execution. -/
lemma measurementSequence_reference_entry {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (classicalOracles.HiddenState × H))
    (refLeft refRight : Reference.Index) :
    (∑ basis : ctx.register.Index,
      ((measurementSequence (allowAllocation := allowAllocation)
        (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles)
          readouts).execute environment
        Reference state).quantumMarginal.matrix
        (basis, refLeft) (basis, refRight)) =
      ∑ basis : ctx.register.Index,
        state.quantumMarginal.matrix (basis, refLeft) (basis, refRight) := by
  induction readouts generalizing H with
  | nil =>
      simp only [measurementSequence, execute_id,
        ExecutionState.mapClassical_quantumMarginal]
  | cons head tail ih =>
      rw [measurementSequence, execute_seq,
        State.mapHistory_quantumMarginal]
      exact (ih ((Circuit.measureZ (allowAllocation := allowAllocation)
        (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) head.wire
        head.output).execute environment Reference state)).trans
        (measurementStep_reference_entry environment (allowAllocation := allowAllocation)
          head state refLeft refRight)

/-- Without borrowed quantum systems, singleton classical input values
and the complete reference are restored. -/
lemma borrowedRestored_measurementSequence_noBorrowedQuantum {ctx : RuntimeCtx .quantum}
    [Subsingleton ctx.borrowedClassicalShape.Value]
    (noQuantum : ctx.borrowedQuantumWires = []) (readouts : List (ZReadout ctx))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (classicalOracles.HiddenState × H)) :
    (measurementSequence (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) readouts).BorrowedRestored
      Reference state
      ((measurementSequence (allowAllocation := allowAllocation)
        (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles)
          readouts).execute environment
        Reference state) := by
  rw [BorrowedRestored, Execution.observeBorrowedAfter_sameContext]
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, refLeft⟩
  rcases column with ⟨right, refRight⟩
  rw [Execution.observeBorrowed_empty_entry_of_subsingleton noQuantum,
    Execution.observeBorrowed_empty_entry_of_subsingleton noQuantum]
  exact measurementSequence_reference_entry environment (allowAllocation := allowAllocation)
    readouts state refLeft refRight

end Circuit

end

end QuantumAlg
