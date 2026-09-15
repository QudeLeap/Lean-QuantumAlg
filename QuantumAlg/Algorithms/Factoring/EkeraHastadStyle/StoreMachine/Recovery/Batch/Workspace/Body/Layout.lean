/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Pairs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Factor.Workspace.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Shared.Initialization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout

/-!
# Physical references for the allocated recovery body

The body receives the actual persistent top cells, the reusable seven-package
pair allocation, and the caller's retained inputs and result destination.
Physical certificates discharge separation; initialization values are supplied
by the actual allocator and shared constant prefix.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody

open Execution
open ClassicalRoutines

noncomputable section

/-- All physical references used by one deepest-scope recovery body. -/
structure Refs {kind : ProblemKind} (root topCtx inner : RuntimeCtx kind) (N : Nat) where
  topTransport : ClassicalWorkspace.Transport root topCtx
  pairTransport : ClassicalWorkspace.Transport topCtx inner
  top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N
  cells : LatticePairFactorWorkspaceSeparation.Cells inner N
  terminals : LatticePairRecoveryBatch.Terminals root N
  parameter : CInputRef root (ParameterShape N)
  result : CWriteRef inner (LatticeBatchRecoveryOutput.OutputShape N)

variable {kind : ProblemKind} {root topCtx inner : RuntimeCtx kind} {N : Nat}

/-- The certificates produced by the real top and seven-package allocation. -/
structure Separation (refs : Refs root topCtx inner N) : Prop where
  topDistinct : refs.top.Distinct
  topSeparated : refs.top.TransportSeparated refs.topTransport
  cells : LatticePairFactorWorkspaceSeparation.Certificates refs.pairTransport refs.cells

/-- Shared modular and quadratic constants use their actual physical destinations. -/
def initializationRefs (refs : Refs root topCtx inner N) :=
  LatticeBatchRecoveryWorkspaceViews.initializationRefs refs.topTransport refs.pairTransport
    refs.cells refs.parameter

/-- The endpoint writes the caller result before any surrounding lexical pop. -/
def endpointRefs (refs : Refs root topCtx inner N) : LatticeBatchRecoveryEndpoint.Refs inner N where
  tail := LatticeBatchRecoveryWorkspaceViews.tailRefs refs.topTransport refs.pairTransport
    refs.top refs.cells refs.terminals refs.parameter
  output := LatticeBatchRecoveryWorkspaceLayout.outputRefs
    (LatticeBatchRecoveryWorkspaceViews.topAt refs.pairTransport refs.top) refs.result
  sharedSelection :=
    LatticeBatchRecoveryWorkspaceViews.factorSelection_topAt refs.pairTransport refs.top

/-- Actual physical certificates discharge both the seeded fold and output separation. -/
theorem endpointSeparation (refs : Refs root topCtx inner N) (separation : Separation refs) :
    LatticeBatchRecoveryEndpoint.Separation (endpointRefs refs) where
  tail := LatticeBatchRecoveryWorkspaceViews.tailSeparation refs.topTransport refs.pairTransport
    refs.top separation.topDistinct separation.topSeparated refs.cells separation.cells
    refs.terminals refs.parameter
  output := LatticeBatchRecoveryWorkspaceLayout.outputSeparation
    (LatticeBatchRecoveryWorkspaceViews.topAt refs.pairTransport refs.top)
    (LatticeBatchRecoveryWorkspaceViews.topAt_distinct refs.pairTransport refs.top
      separation.topDistinct) refs.result

/-- Entry values that the caller parameter and actual top allocation establish. -/
structure InitialConditions (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (refs : Refs root topCtx inner N) (before : Store inner) : Prop where
  initialization :
    LatticeSharedQuadraticInitialization.InitialConditions input before (initializationRefs refs)
  parameterValue : before.read
    (LatticeBatchRecoveryWorkspaceViews.parameterAt refs.topTransport refs.pairTransport
      refs.parameter) = parameterValue input sample
  factorInitiallyClear :
    (before.read (FirstAccepted.cellRead (endpointRefs refs).tail.fold.factorSelection.accepted)
      ).toBool = false

/-- Complete avoidance of the actual shared prefix and endpoint writes. -/
structure CallerFrameAvoids (refs : Refs root topCtx inner N) {shape : CShape}
    (other : CInputRef inner shape) : Prop where
  initialization :
    LatticeSharedQuadraticInitialization.CallerFrameAvoids (initializationRefs refs) other
  endpoint : LatticeBatchRecoveryEndpoint.CallerFrameAvoids (endpointRefs refs) other

/-- The exact original batch value and every disjoint caller value share one actual final store. -/
structure Relation (sample : Fin (2 ^ residueSamplingBits N)) (refs : Refs root topCtx inner N)
    (before after : Store inner) : Prop where
  output : after.read (FirstAccepted.cellRead refs.result) =
    LatticeBatchRecoveryEndpoint.batchOutputValue sample (endpointRefs refs) before
  callerFrame : ∀ {shape : CShape} (other : CInputRef inner shape),
    CallerFrameAvoids refs other → after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody
