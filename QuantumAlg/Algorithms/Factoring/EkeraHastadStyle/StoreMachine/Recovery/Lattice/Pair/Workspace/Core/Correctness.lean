/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Core.Initialization

/-!
# Actual initialized allocation of the three pair-recovery core packages

The shared parameters, candidate slot and persistent pair state receive their
canonical initial values through the actual lexical allocation instructions.
The body's complete execution equation determines the returned caller store.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace

open Execution
open Execution.ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The three actual allocations establish initialization and the caller-store postcondition. -/
theorem withWorkspaces_actualRecord_initialized_post {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (N : Nat)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner N)
      (transport : Transport ctx inner), Certificates transport cells → Circuit inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells),
      ∃ step : Store inner → Store inner × (body cells transport certificates).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body cells transport certificates).execute Reference state =
            state.mapClassical (fun entry =>
              ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
        ∀ before : Store inner, Initialized before cells →
          Post (transport.restrict before) (transport.restrict (step before).1)) :
    ∃ step : Store ctx → Store ctx × (withWorkspaces ctx N body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withWorkspaces ctx N body).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  unfold withWorkspaces
  apply withCells_actualRecord_initialized_restricted_post _ _ _ Post
  intro sharedCtx shared sharedDistinct rootTransport sharedSeparated
  apply withCells_actualRecord_initialized_restricted_post _ _ _
    (fun before after => shared.Initialized before →
      Post (rootTransport.restrict before) (rootTransport.restrict after))
  intro slotCtx slot slotDistinct slotTransport slotSeparated
  apply withCells_actualRecord_initialized_restricted_post _ _ _
    (fun before after => slot.Initialized before →
      shared.Initialized (slotTransport.restrict before) →
      Post (rootTransport.restrict (slotTransport.restrict before))
        (rootTransport.restrict (slotTransport.restrict after)))
  intro stateCtx state stateDistinct stateTransport stateSeparated
  refine Exists.imp ?_ (bodyContract _ _ _)
  intro step contract
  obtain ⟨equation, correct⟩ := contract
  refine ⟨equation, ?_⟩
  intro before stateInitialized slotInitialized sharedInitialized
  have slotInitial := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    stateTransport slot (stateTransport.workspaceTransport_restrict_readsAs before)
    slotInitialized
  have sharedAtSlot := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    slotTransport shared
    (slotTransport.workspaceTransport_restrict_readsAs (stateTransport.restrict before))
    sharedInitialized
  have sharedInitial := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    stateTransport (transportCells slotTransport shared)
    (stateTransport.workspaceTransport_restrict_readsAs before) sharedAtSlot
  simpa only [Transport.workspaceTransport_restrict_compose] using
    correct before ⟨sharedInitial, slotInitial, stateInitialized⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace
