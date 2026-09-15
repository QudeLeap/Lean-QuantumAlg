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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Actual shared constants followed by the original modular setup. -/
def sharedInto (input : Input N) (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto input refs.setup)

/-- Exact actual intermediate stores and chronological paths. -/
def sharedStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (sharedInto input refs).Path :=
  Circuit.sequenceRecord
    (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto input refs.setup)
    (LatticeCandidateConstants.loadStep (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupStep input refs.setup) store

/-- Project the actual resulting store without expanding the program's finite path. -/
theorem sharedStep_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (sharedStep input refs store).1 =
      (LatticeCandidateModularSetup.setupStep input refs.setup
        (LatticeCandidateConstants.loadStep (shortLogBits N) refs.constants store).1).1 :=
  Circuit.sequenceRecord_store _ _ _ _ store

/-- The existing sequence executes the exact record on the complete incoming state. -/
theorem sharedInto_execute (input : Input N) (refs : Refs ctx N)
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (sharedInto input refs).execute Reference state =
      state.mapClassical (fun entry =>
      ((sharedStep input refs entry.1).1, (entry.2, (sharedStep input refs entry.1).2))) := by
  dsimp only [sharedInto, sharedStep]
  exact Circuit.execute_sequenceRecord
    (LatticeCandidateConstants.loadInto (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto input refs.setup)
    (LatticeCandidateConstants.loadStep (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupStep input refs.setup)
    (LatticeCandidateConstants.loadInto_execute (shortLogBits N) refs.constants)
    (LatticeCandidateModularSetup.setupInto_execute input refs.setup) Reference state

/-- Actual pair reduction and both shared initializers. -/
def pairCandidatePrefix (input : Input N) (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair)
    (sharedInto input refs)

/-- Exact actual intermediate stores and chronological paths. -/
def prefixStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (pairCandidatePrefix input refs).Path :=
  Circuit.sequenceRecord
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair)
    (sharedInto input refs)
    (LatticePairNearestPlaneSavedTarget.savedTargetStep refs.pair)
    (sharedStep input refs) store

/-- Project the actual resulting store without expanding the program's finite path. -/
theorem prefixStep_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (prefixStep input refs store).1 =
      (sharedStep input refs
        (LatticePairNearestPlaneSavedTarget.savedTargetStep refs.pair store).1).1 :=
  Circuit.sequenceRecord_store _ _ _ _ store

/-- The existing sequence executes the exact record on the complete incoming state. -/
theorem pairCandidatePrefix_execute (input : Input N) (refs : Refs ctx N)
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pairCandidatePrefix input refs).execute Reference state =
      state.mapClassical (fun entry =>
      ((prefixStep input refs entry.1).1, (entry.2, (prefixStep input refs entry.1).2))) := by
  dsimp only [pairCandidatePrefix, prefixStep]
  exact Circuit.execute_sequenceRecord
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto refs.pair)
    (sharedInto input refs)
    (LatticePairNearestPlaneSavedTarget.savedTargetStep refs.pair)
    (sharedStep input refs)
    (LatticePairNearestPlaneSavedTarget.pairToNearestPlaneSavedTargetInto_execute refs.pair)
    (sharedInto_execute input refs) Reference state

/-- Actual initialized scan following the original complete pair prefix. -/
def pairCandidateRecoveryInto (input : Input N) (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (pairCandidatePrefix input refs)
    (LatticeCandidateScanInitialized.initializedScanInto input refs.scan)

/-- Exact actual intermediate stores and chronological paths. -/
def recoveryStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (pairCandidateRecoveryInto input refs).Path :=
  Circuit.sequenceRecord
    (pairCandidatePrefix input refs)
    (LatticeCandidateScanInitialized.initializedScanInto input refs.scan)
    (prefixStep input refs)
    (LatticeCandidateScanInitialized.initializedStep input refs.scan) store

/-- Project the actual resulting store without expanding the program's finite path. -/
theorem recoveryStep_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (recoveryStep input refs store).1 =
      (LatticeCandidateScanInitialized.initializedStep input refs.scan
        (prefixStep input refs store).1).1 :=
  Circuit.sequenceRecord_store _ _ _ _ store

/-- The existing sequence executes the exact record on the complete incoming state. -/
theorem pairCandidateRecoveryInto_execute (input : Input N) (refs : Refs ctx N)
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pairCandidateRecoveryInto input refs).execute Reference state =
      state.mapClassical (fun entry =>
      ((recoveryStep input refs entry.1).1, (entry.2, (recoveryStep input refs entry.1).2))) := by
  dsimp only [pairCandidateRecoveryInto, recoveryStep]
  exact Circuit.execute_sequenceRecord
    (pairCandidatePrefix input refs)
    (LatticeCandidateScanInitialized.initializedScanInto input refs.scan)
    (prefixStep input refs)
    (LatticeCandidateScanInitialized.initializedStep input refs.scan)
    (pairCandidatePrefix_execute input refs)
    (LatticeCandidateScanInitialized.initializedScanInto_execute input refs.scan) Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
