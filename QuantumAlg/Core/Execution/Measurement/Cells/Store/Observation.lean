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
# Complete-store reference weights of actual measurement-cell allocation

Each actual retained cell initializes its declared value and preserves the
whole earlier store. A weight on the complete allocated store therefore pulls
back through that exact store push. The existing sequence and retention laws
keep both reference coordinates and account for the actual finite history.
-/

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Every complete-store weight follows the actual allocation's initialized store extension. -/
theorem allocate_referenceFiberSum_store (ctx : RuntimeCtx .quantum)
    (dimension : ℕ+) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    ∀ (weight : Store (context ctx dimension count) → ℂ) (leftRef rightRef : Reference.Index),
      ExecutionState.referenceFiberSum ((allocate ctx dimension count).execute Reference state)
          (fun entry _ => weight entry.1) leftRef rightRef =
        ExecutionState.referenceFiberSum state
          (fun entry _ => weight (pushStore dimension count entry.1)) leftRef rightRef := by
  induction count with
  | zero =>
      intro weight leftRef rightRef
      have executed := congrArg
        (fun output : State ctx Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output (fun entry _ => weight entry.1)
            leftRef rightRef)
        (Circuit.execute_id_mapClassical Reference state)
      exact executed.trans (ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2, ()))) (fun entry _ => weight entry.1) leftRef rightRef)
  | succ count induction =>
      intro weight leftRef rightRef
      let middle := context ctx dimension count
      let previous := allocate ctx dimension count
      let retained := Circuit.retain middle middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh
      have sequence := Circuit.referenceFiberSum_execute_seq previous retained state weight
        leftRef rightRef
      have last := Circuit.referenceFiberSum_execute_retain middle.canonicalFreshKey
        (.finite dimension) middle.canonicalFreshKey_fresh
        (previous.execute Reference state) weight leftRef rightRef
      exact sequence.trans (last.trans
        (induction (fun store => weight (store.pushRetained middle.canonicalFreshKey
          (.finite dimension) middle.canonicalFreshKey_fresh)) leftRef rightRef))

end

end QuantumAlg.Execution.MeasurementCells
