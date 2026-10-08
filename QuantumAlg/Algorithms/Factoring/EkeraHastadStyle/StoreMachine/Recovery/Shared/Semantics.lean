/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Shared.Workspace
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted

/-!
# Actual initialized allocation and release of the shared quadratic workspace

Both literal packages receive canonical initial values from the actual lexical
allocation instructions. The complete body execution determines the returned
caller store after release of both packages.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSharedQuadraticWorkspaceSemantics

open Execution
open Execution.ClassicalWorkspace
open LatticeSharedQuadraticWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Canonical shape values in both actual packages before the callback executes. -/
structure Initialized {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (store : Store ctx) (shared : Shared.Cells ctx N)
    (quadratic : Quadratic.Cells ctx N) : Prop where
  shared : shared.Initialized store
  quadratic : quadratic.Initialized store

/-- Actual read agreement preserves initialization of both transported packages. -/
theorem Initialized.transport {kind : ProblemKind} {outer inner : RuntimeCtx kind} {N : Nat}
    {source : Store outer} {before : Store inner} {shared : Shared.Cells outer N}
    {quadratic : Quadratic.Cells outer N} (initial : Initialized source shared quadratic)
    (transport : Transport outer inner) (reads : transport.ReadsAs source before) :
    Initialized before (transportCells transport shared) (transportCells transport quadratic) where
  shared := ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    transport shared reads initial.shared
  quadratic := ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    transport quadratic reads initial.quadratic

/-- Both real allocations establish initialization and the actual returned caller postcondition. -/
theorem withWorkspaces_actualRecord_initialized_post {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) {N : Nat}
    (parameter : CInputRef ctx (ParameterShape N))
    (body : ∀ {inner : RuntimeCtx model.kind}
      (shared : Shared.Cells inner N), shared.Distinct →
      (quadratic : Quadratic.Cells inner N) → quadratic.Distinct →
      (transport : Transport ctx inner) → shared.TransportSeparated transport →
      quadratic.TransportSeparated transport →
      (cross : CrossSeparated shared quadratic) →
      LatticeSharedQuadraticInitialization.Separation
        (refs shared quadratic transport parameter) → Circuit model inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx model.kind}
      (shared : Shared.Cells inner N) (sharedDistinct : shared.Distinct)
      (quadratic : Quadratic.Cells inner N) (quadraticDistinct : quadratic.Distinct)
      (transport : Transport ctx inner) (sharedSeparated : shared.TransportSeparated transport)
      (quadraticSeparated : quadratic.TransportSeparated transport)
      (cross : CrossSeparated shared quadratic)
      (initialization : LatticeSharedQuadraticInitialization.Separation
        (refs shared quadratic transport parameter)),
      ∃ step : Store inner × model.HiddenState →
        (Store inner × model.HiddenState) ×
          (body shared sharedDistinct quadratic quadraticDistinct transport
            sharedSeparated quadraticSeparated cross initialization).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference (model.HiddenState × History)),
          (body shared sharedDistinct quadratic quadraticDistinct transport
            sharedSeparated quadraticSeparated cross initialization).execute Reference state =
              state.mapClassical (fun entry =>
                let actual := step (entry.1, entry.2.1)
                (actual.1.1, (actual.1.2, (entry.2.2, actual.2))))) ∧
        ∀ before : Store inner × model.HiddenState,
          Initialized before.1 shared quadratic →
          Post (transport.restrict before.1) (transport.restrict (step before).1.1)) :
    ∃ step : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (withWorkspaces ctx parameter body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withWorkspaces ctx parameter body).execute Reference state =
          state.mapClassical (fun entry =>
            let actual := step (entry.1, entry.2.1)
            (actual.1.1, (actual.1.2, (entry.2.2, actual.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, Post before.1 (step before).1.1 := by
  unfold withWorkspaces
  apply withCells_actualRecord_initialized_restricted_post _ _ _ Post
  intro sharedCtx shared sharedDistinct rootTransport sharedSeparated
  apply withCells_actualRecord_initialized_restricted_post _ _ _
    (fun before after => shared.Initialized before →
      Post (rootTransport.restrict before) (rootTransport.restrict after))
  intro quadraticCtx quadratic quadraticDistinct innerTransport quadraticSeparated
  refine Exists.imp ?_ (bodyContract _ _ _ _ _ _ _ _ _)
  intro step contract
  obtain ⟨equation, correct⟩ := contract
  refine ⟨equation, ?_⟩
  intro before quadraticInitialized sharedInitialized
  have sharedInitial := ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    innerTransport shared (innerTransport.workspaceTransport_restrict_readsAs before.1)
    sharedInitialized
  simpa only [Transport.workspaceTransport_restrict_compose] using
    correct before ⟨sharedInitial, quadraticInitialized⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSharedQuadraticWorkspaceSemantics
