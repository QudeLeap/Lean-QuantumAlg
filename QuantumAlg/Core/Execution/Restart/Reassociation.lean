/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Restart.Deterministic
import all QuantumAlg.Core.Execution.Circuit.Reassociation

/-!
# The same physical seed under actual sequence reassociation
-/

namespace QuantumAlg.Circuit.RestartCleanup

noncomputable section

open Execution

attribute [local instance] Classical.decEq
attribute [local irreducible] ExecutionState.mapClassical

/-- Only actual sequence parentheses change; every full density block is transported. -/
lemma reassociatedAt {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {source target : Circuit model pre post} (association : Circuit.Reassociation source target)
    (environment : model.Environment)
    (seed : post.quantumLayout.SelectedBasis post.borrowedSelectionᶜ)
    (fixed : ReinitializedAt target environment seed) :
    ReinitializedAt source environment seed := by
  unfold ReinitializedAt at fixed ⊢
  intro Reference History _ state record
  rw [association.toOperationalEquiv.execute]
  unfold State.mapHistory
  exact selectedPureMapDecision post.quantumLayout post.borrowedSelectionᶜ Reference _
    (target.execute environment Reference state) _ (NormalizedVector.ket seed)
    (fixed Reference state) record

end

end QuantumAlg.Circuit.RestartCleanup
