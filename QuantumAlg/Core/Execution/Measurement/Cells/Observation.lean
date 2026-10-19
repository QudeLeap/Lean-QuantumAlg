/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Actual finite-cell allocation preserves earlier weighted reference observations

The existing allocator retains finite classical cells in sequence. Its real
store pushes preserve every structural earlier input, while path regrouping
preserves every weighted reference entry. The allocation leaves the quantum
bank in place and includes the zero-cell boundary.
-/

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
  (environment :
    (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)

/-- Allocating real finite cells preserves all earlier structural-input reference weights. -/
lemma allocate_referenceFiberSum_input {ctx : RuntimeCtx .quantum} {inputShape : CShape}
    (input : CInputRef ctx inputShape) (dimension : ℕ+) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (weight : inputShape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((allocate (model := .quantum gates oracles operations classicalOracles)
          ctx dimension count).execute environment Reference state)
        (fun entry _ => weight (entry.1.read (liftInput dimension input count)))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  induction count with
  | zero =>
      have executed := congrArg
        (fun output : State ctx Reference
            (classicalOracles.HiddenState × (History × Unit)) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
        (Circuit.execute_id_mapClassical (environment := environment) (allowAllocation := true)
          (model := .quantum gates oracles operations classicalOracles) Reference state)
      exact executed.trans (ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
        (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
  | succ count induction =>
      let middle := context ctx dimension count
      let priorInput := liftInput dimension input count
      let allocationPrefix := allocate
        (model := .quantum gates oracles operations classicalOracles) ctx dimension count
      let retention := Circuit.retain
        (model := .quantum gates oracles operations classicalOracles)
        middle middle.canonicalFreshKey (.finite dimension) middle.canonicalFreshKey_fresh
      have sequence := Circuit.referenceFiberSum_execute_seq
        (environment := environment) allocationPrefix retention state
        (fun store => weight (store.read (priorInput.underRetained middle.canonicalFreshKey
          (.finite dimension) middle.canonicalFreshKey_fresh))) leftRef rightRef
      have retained := Circuit.referenceFiberSum_execute_retain_input (environment := environment)
        (gates := gates) (oracles := oracles) (operations := operations)
        (classicalOracles := classicalOracles) priorInput middle.canonicalFreshKey
        (.finite dimension) middle.canonicalFreshKey_fresh
        (allocationPrefix.execute environment Reference state) weight leftRef rightRef
      exact sequence.trans (retained.trans induction)

end

end QuantumAlg.Execution.MeasurementCells
