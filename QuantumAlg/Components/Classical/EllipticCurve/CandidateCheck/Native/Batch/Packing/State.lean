/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Core.Execution.Restart.Retained

/-!
# Actual paid option packing preserves the full completed physical seed
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

attribute [local instance] Classical.decEq
attribute [local irreducible] persistentCtx ExecutionState.mapClassical

/-- The unchanged physical seed is typed once across the actual final retained option cell. -/
def finalPackSeed {kind : ProblemKind} (ctx : RuntimeCtx kind) (width scalar : Nat)
    (seed : (persistentCtx ctx width scalar).quantumLayout.SelectedBasis
      (persistentCtx ctx width scalar).borrowedSelectionᶜ) :
    (batchResultCtx ctx width scalar).quantumLayout.SelectedBasis
      (batchResultCtx ctx width scalar).borrowedSelectionᶜ := seed

/-- The generic actual pack preserves the preceding full physical state on every record. -/
lemma packedReinitializedAt {model : ExecutionModel} {environment : model.Environment}
  [BitWord.Selected model]
    {pre : RuntimeCtx model.kind} (ctx : RuntimeCtx model.kind) (width scalar : Nat)
    (first : Circuit model pre (persistentCtx ctx width scalar))
    (seed : (persistentCtx ctx width scalar).quantumLayout.SelectedBasis
      (persistentCtx ctx width scalar).borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt first environment seed) :
    Circuit.ReinitializedAt ((first.seq (packBatchResult ctx width scalar))) environment
      (finalPackSeed ctx width scalar seed) :=
  Circuit.RestartCleanup.followedByRetainedAt (environment := environment)
    (model := model) (pre := pre) (ctx := persistentCtx ctx width scalar)
    (key := (persistentCtx ctx width scalar).canonicalFreshKey)
    (shape := .option (.unsignedWord scalar))
    (fresh := (persistentCtx ctx width scalar).canonicalFreshKey_fresh) first
    (packBatchResult (model := model) ctx width scalar) seed fixed
    (packBatchResultRecordStep (model := model) ctx width scalar)
    (by
      intro Reference History _ state
      refine (packBatchResult_execute (model := model) ctx width scalar Reference state).trans ?_
      unfold packBatchResultState
      exact ExecutionState.executionState_mapClassical_congr_decision state _ _
        (by intro entry; rfl) _ _)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
