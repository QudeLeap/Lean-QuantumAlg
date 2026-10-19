/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Semantics
import all QuantumAlg.Core.Execution.Restart.Deterministic

/-!
# The actual seven-cell retention preserves every physical seed
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

attribute [local instance] Classical.decEq
attribute [local irreducible] ExecutionState.mapClassical

/-- The actual seven retained destinations leave every previously fixed physical seed unchanged. -/
lemma followedByPersistentAt {model : ExecutionModel} {environment : model.Environment} {pre
  ctx : RuntimeCtx model.kind}
    (first : Circuit model pre ctx) (width scalar : Nat)
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt first environment seed) :
    Circuit.ReinitializedAt ((first.seq (retainPersistent ctx width scalar))) environment seed := by
  unfold Circuit.ReinitializedAt at fixed ⊢
  intro Reference History _ state record
  rw [Circuit.execute_seq]
  unfold State.mapHistory
  apply Circuit.RestartCleanup.selectedPureMapDecision
    (persistentCtx ctx width scalar).quantumLayout
    (persistentCtx ctx width scalar).borrowedSelectionᶜ Reference _
    ((retainPersistent (model := model) ctx width scalar).execute environment Reference
      (first.execute environment Reference state))
    (fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2)))))
    (NormalizedVector.ket seed) _ record
  intro intermediate
  rw [retainPersistent_execute]
  unfold persistentAllocationState
  exact Circuit.RestartCleanup.selectedPureMapDecision ctx.quantumLayout
    ctx.borrowedSelectionᶜ Reference _ (first.execute environment Reference state)
    (fun entry =>
      ((persistentAllocationStep width scalar entry.1).1,
        (entry.2.1, (entry.2.2, (persistentAllocationStep width scalar entry.1).2))))
    (NormalizedVector.ket seed) (fixed Reference state) intermediate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
