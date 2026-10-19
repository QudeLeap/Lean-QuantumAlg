/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Package
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Shared.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Slot.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.State.Workspace.Layout

/-!
# Actual core storage for pair-to-short-log recovery

The shared parameter cells, candidate slot and persistent pair state are
allocated through the existing Circuit workspace instruction. Certificates
follow actual physical identities and the complete support of caller reads.
Quadratic factor reconstruction has its own subsequent workspace boundary.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace

open Execution.ClassicalWorkspace

/-- Three actual typed packages used throughout pair-to-short-log recovery. -/
structure Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  shared : LatticeCandidateSharedWorkspaceLayout.Cells ctx N
  slot : LatticeCandidateSlotWorkspaceLayout.Cells ctx N
  state : LatticePairStateWorkspaceLayout.Cells ctx N

/-- Lift the same physical packages through a further lexical scope. -/
def Cells.transport {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    {N : Nat} (cells : Cells outer N) (transport : Transport outer inner) : Cells inner N where
  shared := transportCells transport cells.shared
  slot := transportCells transport cells.slot
  state := transportCells transport cells.state

/-- Local distinctness, caller-read separation and cross-package physical separation. -/
structure Certificates {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (transport : Transport outer ctx) (cells : Cells ctx N) : Prop where
  sharedDistinct : cells.shared.Distinct
  slotDistinct : cells.slot.Distinct
  stateDistinct : cells.state.Distinct
  sharedSeparated : cells.shared.TransportSeparated transport
  slotSeparated : cells.slot.TransportSeparated transport
  stateSeparated : cells.state.TransportSeparated transport
  sharedSlot : Execution.ClassicalWorkspace.CrossSeparated cells.shared cells.slot
  sharedState : Execution.ClassicalWorkspace.CrossSeparated cells.shared cells.state
  slotState : Execution.ClassicalWorkspace.CrossSeparated cells.slot cells.state

/-- Each core package is physically disjoint from a later scratch package. -/
structure CrossSeparated {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} {shapes : List CShape} (core : Cells ctx N)
    (other : Execution.ClassicalWorkspace.Cells ctx shapes) : Prop where
  shared : Execution.ClassicalWorkspace.CrossSeparated core.shared other
  slot : Execution.ClassicalWorkspace.CrossSeparated core.slot other
  state : Execution.ClassicalWorkspace.CrossSeparated core.state other

/-- Further transport preserves every core-to-scratch key inequality. -/
lemma CrossSeparated.transport {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    {N : Nat} {shapes : List CShape} {core : Cells outer N}
    {other : Execution.ClassicalWorkspace.Cells outer shapes}
    (separated : CrossSeparated core other) (transport : Transport outer inner) :
    CrossSeparated (core.transport transport) (transportCells transport other) where
  shared := separated.shared.transport transport
  slot := separated.slot.transport transport
  state := separated.state.transport transport

/-- Caller-read separation of new scratch separates it from every live core package. -/
lemma crossSeparated_of_nested {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    {N : Nat} {shapes : List CShape} (transport : Transport outer inner)
    (core : Cells outer N) (other : Execution.ClassicalWorkspace.Cells inner shapes)
    (separated : other.TransportSeparated transport) :
    CrossSeparated (core.transport transport) other where
  shared := Execution.ClassicalWorkspace.crossSeparated_of_nested transport
    core.shared other separated
  slot := Execution.ClassicalWorkspace.crossSeparated_of_nested transport core.slot other separated
  state := Execution.ClassicalWorkspace.crossSeparated_of_nested
    transport core.state other separated

/-- Core certificates survive further structural allocation without changing physical keys. -/
lemma Certificates.transport {kind : ProblemKind} {root middle inner : RuntimeCtx kind}
    {N : Nat} {rootTransport : Transport root middle} {cells : Cells middle N}
    (certificates : Certificates rootTransport cells) (transport : Transport middle inner) :
    Certificates (rootTransport.compose transport) (cells.transport transport) where
  sharedDistinct := workspaceCells_transportCells_distinct transport
    cells.shared certificates.sharedDistinct
  slotDistinct := workspaceCells_transportCells_distinct transport
    cells.slot certificates.slotDistinct
  stateDistinct := workspaceCells_transportCells_distinct transport
    cells.state certificates.stateDistinct
  sharedSeparated := workspaceCells_transportCells_transportSeparated rootTransport
    transport cells.shared certificates.sharedSeparated
  slotSeparated := workspaceCells_transportCells_transportSeparated rootTransport
    transport cells.slot certificates.slotSeparated
  stateSeparated := workspaceCells_transportCells_transportSeparated rootTransport
    transport cells.state certificates.stateSeparated
  sharedSlot := certificates.sharedSlot.transport transport
  sharedState := certificates.sharedState.transport transport
  slotState := certificates.slotState.transport transport

/-- Allocate exactly the three core packages used by actual pair-to-short-log execution. -/
def withWorkspaces {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (N : Nat)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner), Certificates transport cells → Circuit model inner inner) :
    Circuit model ctx ctx :=
  withCells ctx (LatticeCandidateSharedWorkspaceLayout.shapes N) fun
      shared sharedDistinct rootTransport sharedSeparated =>
    let sharedPackage : Live rootTransport (LatticeCandidateSharedWorkspaceLayout.shapes N) :=
      ⟨shared, sharedDistinct, sharedSeparated⟩
    withCells _ (LatticeCandidateSlotWorkspaceLayout.shapes N) fun
        slot slotDistinct slotTransport slotInnerSeparated =>
      let slotRootTransport := rootTransport.compose slotTransport
      let sharedAt := sharedPackage.transport slotTransport
      let slotAt : Live slotRootTransport (LatticeCandidateSlotWorkspaceLayout.shapes N) :=
        Live.ofFresh rootTransport slotTransport slot slotDistinct slotInnerSeparated
      let sharedSlotAt := Execution.ClassicalWorkspace.crossSeparated_of_nested
        slotTransport shared slot slotInnerSeparated
      withCells _ (LatticePairStateWorkspaceLayout.shapes N) fun
          state stateDistinct stateTransport stateInnerSeparated =>
        let finalTransport := slotRootTransport.compose stateTransport
        let sharedFinal := sharedAt.transport stateTransport
        let slotFinal := slotAt.transport stateTransport
        let stateFinal : Live finalTransport (LatticePairStateWorkspaceLayout.shapes N) :=
          Live.ofFresh slotRootTransport stateTransport state stateDistinct stateInnerSeparated
        let cells : Cells _ N :=
          { shared := sharedFinal.cells, slot := slotFinal.cells, state := stateFinal.cells }
        let certificates : Certificates finalTransport cells :=
          { sharedDistinct := sharedFinal.distinct
            slotDistinct := slotFinal.distinct
            stateDistinct := stateFinal.distinct
            sharedSeparated := sharedFinal.separated
            slotSeparated := slotFinal.separated
            stateSeparated := stateFinal.separated
            sharedSlot := sharedSlotAt.transport stateTransport
            sharedState := Execution.ClassicalWorkspace.crossSeparated_of_nested
              stateTransport sharedAt.cells state stateInnerSeparated
            slotState := Execution.ClassicalWorkspace.crossSeparated_of_nested
              stateTransport slotAt.cells state stateInnerSeparated }
        body cells finalTransport certificates

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace
