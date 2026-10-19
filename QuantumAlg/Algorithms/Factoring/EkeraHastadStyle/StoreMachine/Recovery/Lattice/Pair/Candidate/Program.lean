/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Layout
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual pair reduction, shared initialization and original candidate scan
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

-- Keep dependent paths folded; generic record laws supply their observations.
attribute [local irreducible] Circuit.sequenceStoreRecord

/-- Actual shared constants followed by the original modular setup. -/
def sharedInto (input : Input N) (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto input refs.setup)

/-- Exact actual intermediate stores and chronological paths. -/
def sharedStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (sharedInto input refs).Path :=
  Circuit.sequenceStoreRecord
    (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto input refs.setup)
    (LatticeCandidateConstants.loadStep (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupStep input refs.setup) store

/-- Project the actual resulting store without expanding the program's finite path. -/
lemma sharedStep_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (sharedStep input refs store).1 =
      (LatticeCandidateModularSetup.setupStep input refs.setup
        (LatticeCandidateConstants.loadStep (shortLogBits N) refs.constants store).1).1 :=
  Circuit.sequenceStoreRecord_store (model := model)
    (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto input refs.setup)
    (LatticeCandidateConstants.loadStep (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupStep input refs.setup) store

/-- The existing sequence executes the exact record on the complete incoming state. -/
lemma sharedInto_execute (input : Input N) (refs : Refs ctx N)
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (sharedInto input refs).execute environment Reference state =
      state.mapClassical (fun entry =>
      let actual := sharedStep input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  exact Circuit.execute_sequenceStoreRecord (environment := environment)
    (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto input refs.setup)
    (LatticeCandidateConstants.loadStep (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupStep input refs.setup)
    (LatticeCandidateConstants.loadInto_execute (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto_execute input refs.setup) Reference state

/-- Actual pair reduction and both shared initializers. -/
def pairCandidatePrefix (input : Input N) (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair)
    (sharedInto input refs)

/-- Exact actual intermediate stores and chronological paths. -/
def prefixStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (pairCandidatePrefix input refs).Path :=
  Circuit.sequenceStoreRecord
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair)
    (sharedInto input refs)
    (LatticePairNearestPlaneSavedTarget.savedTargetStep refs.pair)
    (sharedStep input refs) store

/-- Project the actual resulting store without expanding the program's finite path. -/
lemma prefixStep_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (prefixStep input refs store).1 =
      (sharedStep input refs
        (LatticePairNearestPlaneSavedTarget.savedTargetStep refs.pair store).1).1 :=
  Circuit.sequenceStoreRecord_store (model := model)
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair)
    (sharedInto input refs)
    (LatticePairNearestPlaneSavedTarget.savedTargetStep refs.pair)
    (sharedStep input refs) store

/-- The existing sequence executes the exact record on the complete incoming state. -/
lemma pairCandidatePrefix_execute (input : Input N) (refs : Refs ctx N)
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pairCandidatePrefix input refs).execute environment Reference state =
      state.mapClassical (fun entry =>
      let actual := prefixStep input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  exact Circuit.execute_sequenceStoreRecord (environment := environment)
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair)
    (sharedInto input refs)
    (LatticePairNearestPlaneSavedTarget.savedTargetStep refs.pair)
    (sharedStep input refs)
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_execute refs.pair)
    (sharedInto_execute input refs) Reference state

/-- Actual initialized scan following the original complete pair prefix. -/
def pairCandidateRecoveryInto (input : Input N) (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (pairCandidatePrefix input refs)
    (LatticeCandidateScanInitialized.initializedScanInto input refs.scan)

/-- Exact actual intermediate stores and chronological paths.
This mathematical record retains the full path without native extraction. -/
noncomputable def recoveryStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (pairCandidateRecoveryInto input refs).Path :=
  Circuit.sequenceStoreRecord
    (pairCandidatePrefix input refs)
    (LatticeCandidateScanInitialized.initializedScanInto input refs.scan)
    (prefixStep input refs)
    (LatticeCandidateScanInitialized.initializedStep input refs.scan) store

/-- Project the actual resulting store without expanding the program's finite path. -/
lemma recoveryStep_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (recoveryStep input refs store).1 =
      (LatticeCandidateScanInitialized.initializedStep input refs.scan
        (prefixStep input refs store).1).1 :=
  Circuit.sequenceStoreRecord_store (model := model)
    (pairCandidatePrefix input refs)
    (LatticeCandidateScanInitialized.initializedScanInto input refs.scan)
    (prefixStep input refs)
    (LatticeCandidateScanInitialized.initializedStep input refs.scan) store

/-- The existing sequence executes the exact record on the complete incoming state. -/
lemma pairCandidateRecoveryInto_execute (input : Input N) (refs : Refs ctx N)
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pairCandidateRecoveryInto input refs).execute environment Reference state =
      state.mapClassical (fun entry =>
      let actual := recoveryStep input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  exact Circuit.execute_sequenceStoreRecord (environment := environment)
    (pairCandidatePrefix input refs)
    (LatticeCandidateScanInitialized.initializedScanInto input refs.scan)
    (prefixStep input refs)
    (LatticeCandidateScanInitialized.initializedStep input refs.scan)
    (pairCandidatePrefix_execute input refs)
    (LatticeCandidateScanInitialized.initializedScanInto_execute input refs.scan) Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
