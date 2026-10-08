/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program

/-!
# Complete caller reads through actual pair-candidate initialization
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Both actual shared initializers preserve every read outside their original destinations. -/
theorem sharedInto_callerFrame (input : Input N) (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (constants : AvoidsConstantWrites refs other) (setup : AvoidsSetupWrites refs other) :
    (sharedStep input refs store).1.read other = store.read other := by
  rw [sharedStep_store]
  exact (LatticeCandidateModularSetup.setupInto_callerFrame input refs.setup _ other setup).trans
    (LatticeCandidateConstants.loadInto_callerFrame (shortLogBits N) refs.constants store
      other constants.1 constants.2)

/-- The actual complete pair prefix preserves each caller read outside its three footprints. -/
theorem pairCandidatePrefix_callerFrame (input : Input N) (refs : Refs ctx N)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : CallerFrameAvoids refs other) :
    (prefixStep input refs store).1.read other = store.read other := by
  rw [prefixStep_store]
  exact (sharedInto_callerFrame input refs _ other separate.constants separate.setup).trans
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_callerFrame
      refs.pair store other separate.pair)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
