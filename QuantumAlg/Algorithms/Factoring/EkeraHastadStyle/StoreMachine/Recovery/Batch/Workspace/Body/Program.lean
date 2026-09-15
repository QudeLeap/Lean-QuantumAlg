/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Shared.Initialization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Endpoint
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual shared initialization followed by the complete batch endpoint

The endpoint receives the actual store emitted by shared initialization. The
record retains both chronological paths and writes the complete optional result
inside the still-live allocation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {root topCtx inner : RuntimeCtx kind} {N : Nat}

/-- Run the shared constant prefix, every pair, and the caller output packing in order. -/
def into (input : Input N) (refs : Refs root topCtx inner N) : Circuit inner inner :=
  .seq (LatticeSharedQuadraticInitialization.into input (initializationRefs refs))
    (LatticeBatchRecoveryEndpoint.into input (endpointRefs refs))

/-- Actual full store and both chronological paths of the allocated body. -/
def step (input : Input N) (refs : Refs root topCtx inner N) (store : Store inner) :
    Store inner × (into input refs).Path :=
  Circuit.sequenceRecord
    (LatticeSharedQuadraticInitialization.into input (initializationRefs refs))
    (LatticeBatchRecoveryEndpoint.into input (endpointRefs refs))
    (LatticeSharedQuadraticInitialization.step input (initializationRefs refs))
    (LatticeBatchRecoveryEndpoint.step input (endpointRefs refs)) store

/-- The actual endpoint store follows the actual initialization store. -/
theorem step_store (input : Input N) (refs : Refs root topCtx inner N) (store : Store inner) :
    (step input refs store).1 =
      (LatticeBatchRecoveryEndpoint.step input (endpointRefs refs)
        (LatticeSharedQuadraticInitialization.step input (initializationRefs refs) store).1).1 :=
  Circuit.sequenceRecord_store _ _ _ _ store

/-- Both phases execute on the full incoming history and arbitrary external reference. -/
theorem into_execute (input : Input N) (refs : Refs root topCtx inner N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State inner Reference History) :
    (into input refs).execute Reference state = state.mapClassical (fun entry =>
      ((step input refs entry.1).1, (entry.2, (step input refs entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _
    (LatticeSharedQuadraticInitialization.into_execute input (initializationRefs refs))
    (LatticeBatchRecoveryEndpoint.into_execute input (endpointRefs refs)) Reference state

/-- Every caller read disjoint from both actual stages retains its complete input value. -/
theorem into_callerFrame (input : Input N) (refs : Refs root topCtx inner N) (store : Store inner)
    {shape : CShape} (other : CInputRef inner shape) (avoids : CallerFrameAvoids refs other) :
    (step input refs store).1.read other = store.read other := by
  rw [step_store]
  exact (LatticeBatchRecoveryEndpoint.into_callerFrame input (endpointRefs refs) _ other
    avoids.endpoint).trans
    (LatticeSharedQuadraticInitialization.into_callerFrame input (initializationRefs refs)
      store other avoids.initialization)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody
