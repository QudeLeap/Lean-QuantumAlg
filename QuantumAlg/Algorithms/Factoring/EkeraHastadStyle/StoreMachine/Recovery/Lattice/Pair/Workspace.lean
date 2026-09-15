/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Core
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Workspace.Layout

/-!
# Actual physical allocation for pair-to-short-log recovery

Three persistent core packages and the target, LLL and nearest-plane scratch
packages are allocated through the existing Circuit instruction. Every local,
caller and cross-package certificate follows their actual storage identities.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace

open Execution.ClassicalWorkspace

/-- All six actual packages needed by one reusable pair recovery. -/
structure Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the core stage. -/
  core : LatticePairCoreWorkspace.Cells ctx N
  /-- Nested references for the target stage. -/
  target : LatticeWideTargetWorkspaceLayout.Cells ctx N
  /-- Nested references for the lll stage. -/
  lll : LatticeFixedFuelScratchWorkspaceLayout.Cells ctx N
  /-- Nested references for the nearest stage. -/
  nearest : LatticeNearestPlaneScratchWorkspaceLayout.Cells ctx N

/-- Complete physical separation certificate for the six actual packages. -/
structure Certificates {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx) (cells : Cells ctx N) : Prop where
  core : LatticePairCoreWorkspace.Certificates transport cells.core
  targetDistinct : cells.target.Distinct
  lllDistinct : cells.lll.Distinct
  nearestDistinct : cells.nearest.Distinct
  targetSeparated : cells.target.TransportSeparated transport
  lllSeparated : cells.lll.TransportSeparated transport
  nearestSeparated : cells.nearest.TransportSeparated transport
  coreTarget : LatticePairCoreWorkspace.CrossSeparated
    cells.core cells.target
  coreLll : LatticePairCoreWorkspace.CrossSeparated cells.core cells.lll
  coreNearest : LatticePairCoreWorkspace.CrossSeparated
    cells.core cells.nearest
  targetLll : Execution.ClassicalWorkspace.CrossSeparated cells.target cells.lll
  targetNearest : Execution.ClassicalWorkspace.CrossSeparated
    cells.target cells.nearest
  lllNearest : Execution.ClassicalWorkspace.CrossSeparated cells.lll cells.nearest

/-- Allocate every reusable package required by one pair recovery. -/
def withWorkspaces {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner N)
      (transport : Transport ctx inner),
      Certificates transport cells → Circuit inner inner) :
    Circuit ctx ctx :=
  LatticePairCoreWorkspace.withWorkspaces ctx N fun
      core coreTransport coreCertificates =>
    withCells _
        (LatticeWideTargetWorkspaceLayout.shapes N) fun
        target targetDistinct targetTransport targetInnerSeparated =>
      let targetRootTransport := Transport.compose
        coreTransport targetTransport
      let coreAtTarget := core.transport targetTransport
      let coreCertificatesAtTarget := coreCertificates.transport targetTransport
      let targetAt : Execution.ClassicalWorkspace.Live targetRootTransport
          (LatticeWideTargetWorkspaceLayout.shapes N) :=
        Execution.ClassicalWorkspace.Live.ofFresh coreTransport targetTransport target
          targetDistinct targetInnerSeparated
      let coreTargetAt := LatticePairCoreWorkspace.crossSeparated_of_nested
        targetTransport core target targetInnerSeparated
      withCells _
          (LatticeFixedFuelScratchWorkspaceLayout.shapes N) fun
          lll lllDistinct lllTransport lllInnerSeparated =>
        let lllRootTransport := Transport.compose
          targetRootTransport lllTransport
        let coreAtLll := coreAtTarget.transport lllTransport
        let coreCertificatesAtLll :=
          coreCertificatesAtTarget.transport lllTransport
        let targetAtLll := targetAt.transport lllTransport
        let lllAt : Execution.ClassicalWorkspace.Live lllRootTransport
            (LatticeFixedFuelScratchWorkspaceLayout.shapes N) :=
          Execution.ClassicalWorkspace.Live.ofFresh targetRootTransport lllTransport
            lll lllDistinct lllInnerSeparated
        let coreTargetAtLll := coreTargetAt.transport lllTransport
        let coreLllAt := LatticePairCoreWorkspace.crossSeparated_of_nested
          lllTransport coreAtTarget lll lllInnerSeparated
        let targetLllAt := Execution.ClassicalWorkspace.crossSeparated_of_nested
          lllTransport targetAt.cells lll lllInnerSeparated
        withCells _
            (LatticeNearestPlaneScratchWorkspaceLayout.shapes N) fun
            nearest nearestDistinct nearestTransport nearestInnerSeparated =>
          let finalTransport := Transport.compose
            lllRootTransport nearestTransport
          let coreFinal := coreAtLll.transport nearestTransport
          let coreCertificatesFinal :=
            coreCertificatesAtLll.transport nearestTransport
          let targetFinal := targetAtLll.transport nearestTransport
          let lllFinal := lllAt.transport nearestTransport
          let nearestFinal : Execution.ClassicalWorkspace.Live finalTransport
              (LatticeNearestPlaneScratchWorkspaceLayout.shapes N) :=
            Execution.ClassicalWorkspace.Live.ofFresh lllRootTransport
              nearestTransport nearest nearestDistinct nearestInnerSeparated
          let cells : Cells _ N :=
            { core := coreFinal
              target := targetFinal.cells
              lll := lllFinal.cells
              nearest := nearestFinal.cells }
          let certificates : Certificates finalTransport cells :=
            { core := coreCertificatesFinal
              targetDistinct := targetFinal.distinct
              lllDistinct := lllFinal.distinct
              nearestDistinct := nearestFinal.distinct
              targetSeparated := targetFinal.separated
              lllSeparated := lllFinal.separated
              nearestSeparated := nearestFinal.separated
              coreTarget := coreTargetAtLll.transport nearestTransport
              coreLll := coreLllAt.transport nearestTransport
              coreNearest :=
                LatticePairCoreWorkspace.crossSeparated_of_nested
                  nearestTransport coreAtLll nearest nearestInnerSeparated
              targetLll := targetLllAt.transport nearestTransport
              targetNearest :=
                Execution.ClassicalWorkspace.crossSeparated_of_nested
                  nearestTransport targetAtLll.cells nearest
                    nearestInnerSeparated
              lllNearest := Execution.ClassicalWorkspace.crossSeparated_of_nested
                nearestTransport lllAt.cells nearest nearestInnerSeparated }
          body cells finalTransport certificates

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace
