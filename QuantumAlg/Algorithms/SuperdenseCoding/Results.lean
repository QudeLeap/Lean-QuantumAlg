/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Correctness
import all QuantumAlg.Algorithms.SuperdenseCoding.Correctness
import all QuantumAlg.Algorithms.SuperdenseCoding.Admission
import all QuantumAlg.Algorithms.SuperdenseCoding.Specification
import all QuantumAlg.Algorithms.SuperdenseCoding.Geometry
import all QuantumAlg.Algorithms.SuperdenseCoding.Construction
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Complete superdense-coding success, state and restoration results

These conclusions use the real input cells, the real result cells and the
same complete native run. Borrowed classical values retain all correlations
with an arbitrary reference. The independent source communication profile
remains in the mathematical support module; no transmission instruction is
claimed for an execution language without a send operation
[dW19, qcnotes.tex:879-890].
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq Classical.propDecidable

/-- All actual positive records decode the admitted message, giving probability exactly one. -/
public lemma superdense_success
    (environment : model.Environment) (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} (input : OracleInput .empty (context count) Reference)
    (valid : admissible count bits input.caller.localState) :
    (1 : ENNReal) ≤ (((algorithm count).relationalDistribution environment) input).toOuterMeasure
      {pair | pair.2 = messageValue bits} := by
  apply le_of_eq
  symm
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro pair supported
  change pair ∈ ((((algorithm count).run.executionDistribution environment) input).map
    (fun record => (record.2.2.1, (algorithm count).run.result record))).support at supported
  obtain ⟨record, recorded, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have positive := (ExecutionState.mem_support_toPMF_iff
    (((algorithm count).run.execute environment) Reference input.state)
    (((algorithm count).run.execute_normalized environment) input) record).mp recorded
  have decoded := superdense_run_output_of_positive environment count bits input valid record
    positive
  have result := congrArg Prod.snd same
  exact result.symm.trans decoded

/-- The exact independent state obligation holds on the full original frame and reference. -/
public lemma superdense_states
    (environment : model.Environment) (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} (input : OracleInput .empty (context count) Reference)
    (valid : admissible count bits input.caller.localState) :
    (stateRequirement count bits).Holds input.caller
      (((algorithm count).run.finalState environment) Reference input.state) := by
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed
        (StateRequirement.unitaryTarget (physicalOperator count bits) Reference input.caller)
        (StateRequirement.unitaryTarget_normalized
          (physicalOperator count bits) Reference input.caller)).Holds
          (DensityOperator.observeSelectionWithReference (context count).quantumLayout
            Finset.univ Reference
            (((((algorithm count).run.finalState environment) Reference input.state).mapClassical
              (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block,
        superdense_finalState_quantumMarginal environment count bits input valid]
      change (StateRequirement.unitaryTarget
        (physicalOperator count bits) Reference input.caller).matrix =
        ((StateRequirement.unitaryTarget
          (physicalOperator count bits) Reference input.caller).mass : ℝ) • _
      rw [StateRequirement.unitaryTarget_normalized]
      simp only [one_smul]

private lemma cells_noBorrowedQuantum (ctx : RuntimeCtx .quantum)
    (empty : ctx.borrowedQuantumWires = []) (count : Nat) :
    (MeasurementCells.context ctx 2 count).borrowedQuantumWires = [] := by
  induction count with
  | zero => exact empty
  | succ count ih =>
      rw [MeasurementCells.context, RuntimeCtx.borrowedQuantumWires_addRetained]
      exact ih

private lemma noBorrowedQuantum (count : Nat) : (context count).borrowedQuantumWires = [] :=
  cells_noBorrowedQuantum (inputContext count) rfl (width count)

/-- Borrowed message cells and their full reference correlations survive every actual operation. -/
public lemma superdense_borrowed (environment : model.Environment) (count : Nat)
    {Reference : Register} (input : OracleInput .empty (context count) Reference) :
    ((algorithm count).run.RestoresBorrowed environment) input := by
  change observeBorrowedAfter (code count) Reference
    (((code count).execute environment) Reference (entered count input))
      = observeBorrowed Reference input.state
  refine ((code count).borrowedRestored_of_noBorrowedQuantum
    environment (noBorrowedQuantum count) Reference (entered count input)).trans ?_
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block]
  change (context count).observeBorrowedWithReference Reference
      (((input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))).mapClassical
        (fun entry => entry.1.readBorrowedClassical)).block value) = _
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  rfl

end
end QuantumAlg.SuperdenseCoding.Execution
