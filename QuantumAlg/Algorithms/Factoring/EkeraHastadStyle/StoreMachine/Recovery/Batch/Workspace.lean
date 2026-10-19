/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Space

/-!
# Actual lexical workspace for fixed-batch recovery

The persistent six-cell batch state is allocated first. The original six pair
packages follow, then an independent twenty-six-cell quadratic package. All
120 pairs reuse this same allocation before lexical release returns the caller store.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspace

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

/-- The retained parameter viewed inside the persistent top workspace. -/
def parameterAt {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (parameter : CInputRef outer (ParameterShape N)) :
    CInputRef ctx (ParameterShape N) :=
  transport.liftInput parameter

/-- The retained terminals viewed inside the persistent top workspace. -/
def terminalsAt {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx)
    (terminals : LatticePairRecoveryBatch.Terminals outer N) :
    LatticePairRecoveryBatch.Terminals ctx N :=
  LatticePairRecoveryFoldWorkspace.liftTerminals transport terminals

/-- Fresh top cells frame the parameter and both terminals of every pair. -/
lemma factorFrames {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells ctx N)
    (transport : Transport outer ctx)
    (separated : top.TransportSeparated transport)
    (terminals : LatticePairRecoveryBatch.Terminals outer N)
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticePairRecoveryFoldWorkspace.FactorFrameAvoids
      (LatticeBatchRecoveryWorkspaceLayout.factorSelection top)
      (terminalsAt transport terminals) (parameterAt transport parameter) := by
  have factorAvoids {shape : CShape} (input : CInputRef outer shape)
      (cell : QuadraticCheckSeparation.FactorCell) :
      (QuadraticCheckSeparation.factorKey
        (LatticeBatchRecoveryWorkspaceLayout.factorSelection top) cell) ∉
          (transport.liftInput input).storageKeys := by
    cases cell with
    | accepted =>
        simpa only [QuadraticCheckSeparation.factorKey,
          LatticeBatchRecoveryWorkspaceLayout.factorSelection,
          LatticeBatchRecoveryWorkspaceLayout.accepted] using
            (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids top transport separated
              input (LatticeBatchRecoveryWorkspaceLayout.acceptedIndex N))
    | selected =>
        simpa only [QuadraticCheckSeparation.factorKey,
          LatticeBatchRecoveryWorkspaceLayout.factorSelection,
          LatticeBatchRecoveryWorkspaceLayout.selected] using
            (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids top transport separated
              input (LatticeBatchRecoveryWorkspaceLayout.selectedIndex N))
    | available =>
        simpa only [QuadraticCheckSeparation.factorKey,
          LatticeBatchRecoveryWorkspaceLayout.factorSelection,
          LatticeBatchRecoveryWorkspaceLayout.available] using
            (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids top transport separated
              input (LatticeBatchRecoveryWorkspaceLayout.availableIndex N))
    | take =>
        simpa only [QuadraticCheckSeparation.factorKey,
          LatticeBatchRecoveryWorkspaceLayout.factorSelection,
          LatticeBatchRecoveryWorkspaceLayout.take] using
            (ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids top transport separated
              input (LatticeBatchRecoveryWorkspaceLayout.takeIndex N))
  refine {
    parameter := ?_
    first := ?_
    second := ?_ }
  · intro cell
    exact factorAvoids parameter cell
  · intro index cell
    unfold terminalsAt
    rw [LatticePairRecoveryFoldWorkspace.terminalPairs_lift]
    simp only [List.Vector.get_map]
    exact factorAvoids
      ((LatticePairRecoveryBatch.terminalPairs terminals).get index).1 cell
  · intro index cell
    unfold terminalsAt
    rw [LatticePairRecoveryFoldWorkspace.terminalPairs_lift]
    simp only [List.Vector.get_map]
    exact factorAvoids
      ((LatticePairRecoveryBatch.terminalPairs terminals).get index).2 cell

/-- Allocate persistent batch state, the original six pair packages and quadratic scratch. -/
def withWorkspaces {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (N : Nat)
    (body : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N), top.Distinct →
      (topTransport : Transport ctx topCtx) → top.TransportSeparated topTransport →
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N) →
      (pairTransport : Transport topCtx inner) →
      LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells →
        Circuit model inner inner) :
    Circuit model ctx ctx :=
  withCells ctx (LatticeBatchRecoveryWorkspaceLayout.topShapes N) fun
      top topDistinct topTransport topSeparated =>
    LatticePairRecoveryWorkspace.withWorkspaces _ N fun pair pairTransport pairCertificates =>
      withCells _ (QuadraticScratchLayout.shapes N) fun
          quadratic quadraticDistinct quadraticTransport quadraticSeparated =>
        body top topDistinct topTransport topSeparated
          (LatticePairFactorWorkspaceSeparation.Cells.ofNested pair quadraticTransport quadratic)
          (pairTransport.compose quadraticTransport)
          (LatticePairFactorWorkspaceSeparation.Certificates.ofNested pairTransport
            quadraticTransport pair pairCertificates quadratic quadraticDistinct quadraticSeparated)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspace
