/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Shared.Workspace
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Shared.Workspace.Layout

/-!
# Actual shared-prefix preservation of caller and persistent top storage

Every shared or quadratic destination belongs to a fresh package below the top
scope. Its allocation certificate therefore frames all transported top inputs,
including retained terminal bits and the persistent first-success latch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody

open Execution
open ClassicalRoutines

noncomputable section

variable {additionalMembers : Nat}

variable {kind : ProblemKind} {root topCtx inner : RuntimeCtx kind} {N : Nat}

/-- Fresh shared destinations avoid every input transported from the persistent top scope. -/
private lemma setup_avoids_topInput (refs : Refs root topCtx inner N additionalMembers)
    (separation : Separation refs) {shape : CShape} (other : CInputRef topCtx shape)
    (cell : LatticeCandidateModularSetup.MutableCell) :
    LatticeCandidateModularSetup.mutableKey (initializationRefs refs).setup cell ∉
      (refs.pairTransport.liftInput other).storageKeys := by
  have keyEq : LatticeCandidateModularSetup.mutableKey (initializationRefs refs).setup cell =
      (ClassicalWorkspace.cellAt refs.cells.pair.core.shared
        (LatticeCandidateSharedWorkspaceLayout.setupIndex N cell)).ref.toCStorageRef.key := by
    simpa only [initializationRefs, LatticeBatchRecoveryWorkspaceViews.initializationRefs,
      LatticeSharedQuadraticWorkspace.refs] using
      (LatticeCandidateSharedWorkspaceLayout.setupMutableKey refs.cells.pair.core.shared
        (LatticeBatchRecoveryWorkspaceViews.deepTransport refs.topTransport refs.pairTransport)
        refs.parameter cell)
  rw [keyEq]
  exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
    refs.cells.pair.core.shared refs.pairTransport separation.cells.pair.core.sharedSeparated
    other (LatticeCandidateSharedWorkspaceLayout.setupIndex N cell)

/-- Every top-scope input avoids both actual stages of shared initialization. -/
lemma initializationCallerFrame_of_topInput (refs : Refs root topCtx inner N additionalMembers)
    (separation : Separation refs) {shape : CShape} (other : CInputRef topCtx shape) :
    LatticeSharedQuadraticInitialization.CallerFrameAvoids (initializationRefs refs)
      (refs.pairTransport.liftInput other) := by
  have quadraticAvoids (cell : QuadraticScratchLayout.Cell) :
      (QuadraticScratchLayout.cellRef refs.cells.quadratic cell).key ∉
        (refs.pairTransport.liftInput other).storageKeys :=
    ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids refs.cells.quadratic
      refs.pairTransport separation.cells.quadraticSeparated other
      (QuadraticScratchLayout.cellIndex N cell)
  exact ⟨setup_avoids_topInput refs separation other,
    quadraticAvoids .modulus, quadraticAvoids .one, quadraticAvoids .zero⟩

/-- Every original caller input survives the shared initialization prefix. -/
lemma initializationCallerFrame_of_rootInput (refs : Refs root topCtx inner N additionalMembers)
    (separation : Separation refs) {shape : CShape} (other : CInputRef root shape) :
    LatticeSharedQuadraticInitialization.CallerFrameAvoids (initializationRefs refs)
      ((refs.topTransport.compose refs.pairTransport).liftInput other) := by
  simpa only [ClassicalWorkspace.Transport.liftInput_compose] using
    initializationCallerFrame_of_topInput refs separation (refs.topTransport.liftInput other)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody
