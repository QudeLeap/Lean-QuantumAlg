/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.NearestPlane.SavedTarget.Resources.Budget

/-!
# Independent native coordinate budget for complete pair-candidate recovery

The formulas compose the original pair reduction, shared initializers, and
initialized candidate scan. Each component allowance is stated independently
of actual stored values, branch decisions, and execution resource ledgers.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Independent allowance for shared constants and the original modular setup. -/
def sharedEventEnvelope (N : Nat) : ResourcePool model :=
  ResourcePool.ofList (LatticeCandidateConstants.loadTrace (shortLogBits N) (Width N)) +
    LatticeCandidateModularSetup.setupEventEnvelope model (modulusBits N)

/-- Independent allowance for original pair reduction and both shared initializers. -/
def prefixEventEnvelope (N : Nat) : ResourcePool model :=
  LatticePairNearestPlaneSavedTarget.eventEnvelope N + sharedEventEnvelope N

/-- Independent full allowance includes every slot of the original initialized candidate scan. -/
def recoveryEventEnvelope (N : Nat) : ResourcePool model :=
  prefixEventEnvelope N + LatticeCandidateScanInitialized.initializedScanEventEnvelope model N
    (shortLogBits N) (tradeoffBits N)

/-- Actual shared initialization satisfies its independent complete coordinate allowance. -/
lemma sharedInto_pool_le (input : Input N) (refs : Refs ctx N)
    (path : (sharedInto input refs).Path) :
    (sharedInto input refs).resourcePool path ≤ sharedEventEnvelope N := by
  have constants := LatticeCandidateConstants.loadInto_resourcePool
    (shortLogBits N) refs.constants path.1
  have setup : (LatticeCandidateModularSetup.setupInto input refs.setup).resourcePool path.2 ≤
      LatticeCandidateModularSetup.setupEventEnvelope model (modulusBits N) :=
    LatticeCandidateModularSetup.setupInto_pool_le input refs.setup path.2
  unfold sharedEventEnvelope
  rw [sharedInto_resourcePool]
  exact add_le_add constants.le setup

/-- Every actual pair prefix satisfies the independent reduction and initialization allowance. -/
lemma pairCandidatePrefix_pool_le (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidatePrefix input refs).Path) :
    (pairCandidatePrefix input refs).resourcePool path ≤ prefixEventEnvelope N := by
  have pair :
      (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair).resourcePool
        path.1 ≤ LatticePairNearestPlaneSavedTarget.eventEnvelope N :=
    LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_pool_le refs.pair path.1
  have shared : (sharedInto input refs).resourcePool path.2 ≤ sharedEventEnvelope N :=
    sharedInto_pool_le input refs path.2
  unfold prefixEventEnvelope
  rw [pairCandidatePrefix_resourcePool]
  exact add_le_add pair shared

/-- Every complete actual pair-candidate path meets the independent native coordinate budget. -/
lemma pairCandidateRecoveryInto_pool_le (input : Input N) (refs : Refs ctx N)
    (path : (pairCandidateRecoveryInto input refs).Path) :
    (pairCandidateRecoveryInto input refs).resourcePool path ≤ recoveryEventEnvelope N := by
  have prefixBound : (pairCandidatePrefix input refs).resourcePool path.1 ≤ prefixEventEnvelope N :=
    pairCandidatePrefix_pool_le input refs path.1
  have scan :
      (LatticeCandidateScanInitialized.initializedScanInto input refs.scan).resourcePool path.2 ≤
      LatticeCandidateScanInitialized.initializedScanEventEnvelope model N (shortLogBits N)
        (tradeoffBits N) :=
    LatticeCandidateScanInitialized.initializedScanInto_pool_le input refs.scan path.2
  unfold recoveryEventEnvelope
  rw [pairCandidateRecoveryInto_resourcePool]
  exact add_le_add prefixBound scan

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
