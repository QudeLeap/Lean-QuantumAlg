/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Uniform

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Core.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Initialization

/-!
# Actual initialized allocation of all six pair-recovery packages

Core, target, LLL and nearest-plane allocation supplies the canonical initial
values used by the body. Restriction follows the actual nested caller stores,
so the postcondition holds on the store returned by lexical release.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace

open Execution
open Execution.ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Six actual package allocations supply initialization and return the caller postcondition. -/
lemma withWorkspaces_actualRecord_initialized_post {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (N : Nat)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner), Certificates transport cells → Circuit model inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells),
      ∃ step : Store inner → Store inner × (body cells transport certificates).Path,
        (∀ (environment : model.Environment) (Reference : Register) {History : Type} [Fintype
          History]
          (state : State inner Reference (model.HiddenState × History)),
          (body cells transport certificates).execute environment Reference state =
            state.mapClassical (fun entry =>
              ((step entry.1).1, (entry.2.1, (entry.2.2, (step entry.1).2))))) ∧
        ∀ before : Store inner, Initialized before cells →
          Post (transport.restrict before) (transport.restrict (step before).1)) :
    ∃ step : Store ctx → Store ctx × (withWorkspaces ctx N body).Path,
      (∀ (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withWorkspaces ctx N body).execute environment Reference state =
          state.mapClassical (fun entry =>
          ((step entry.1).1, (entry.2.1, (entry.2.2, (step entry.1).2))))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  unfold withWorkspaces
  apply LatticePairCoreWorkspace.withWorkspaces_actualRecord_initialized_post _ _ _ Post
  intro coreCtx core coreTransport coreCertificates
  apply withCells_actualStoreRecord_initialized_uniform_restricted_post _ _ _
    (fun before after => LatticePairCoreWorkspace.Initialized before core →
      Post (coreTransport.restrict before) (coreTransport.restrict after))
  intro targetCtx target targetDistinct targetTransport targetSeparated
  apply withCells_actualStoreRecord_initialized_uniform_restricted_post _ _ _
    (fun before after => target.Initialized before →
      LatticePairCoreWorkspace.Initialized (targetTransport.restrict before) core →
      Post (coreTransport.restrict (targetTransport.restrict before))
        (coreTransport.restrict (targetTransport.restrict after)))
  intro lllCtx lll lllDistinct lllTransport lllSeparated
  apply withCells_actualStoreRecord_initialized_uniform_restricted_post _ _ _
    (fun before after => lll.Initialized before →
      target.Initialized (lllTransport.restrict before) →
      LatticePairCoreWorkspace.Initialized
        (targetTransport.restrict (lllTransport.restrict before)) core →
      Post (coreTransport.restrict (targetTransport.restrict (lllTransport.restrict before)))
        (coreTransport.restrict (targetTransport.restrict (lllTransport.restrict after))))
  intro nearestCtx nearest nearestDistinct nearestTransport nearestSeparated
  refine Exists.imp ?_ (bodyContract _ _ _)
  intro step contract
  obtain ⟨equation, correct⟩ := contract
  refine ⟨equation, ?_⟩
  intro before nearestInitialized lllInitialized targetInitialized coreInitialized
  have lllInitial := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    nearestTransport lll (nearestTransport.workspaceTransport_restrict_readsAs before)
    lllInitialized
  have targetAtLll := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    lllTransport target
    (lllTransport.workspaceTransport_restrict_readsAs (nearestTransport.restrict before))
    targetInitialized
  have targetInitial := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    nearestTransport (transportCells lllTransport target)
    (nearestTransport.workspaceTransport_restrict_readsAs before) targetAtLll
  have coreAtTarget := coreInitialized.transport targetTransport
    (targetTransport.workspaceTransport_restrict_readsAs
      (lllTransport.restrict (nearestTransport.restrict before)))
  have coreAtLll := coreAtTarget.transport lllTransport
    (lllTransport.workspaceTransport_restrict_readsAs (nearestTransport.restrict before))
  have coreInitial := coreAtLll.transport nearestTransport
    (nearestTransport.workspaceTransport_restrict_readsAs before)
  simpa only [Transport.workspaceTransport_restrict_compose] using
    correct before ⟨coreInitial, targetInitial, lllInitial, nearestInitialized⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace
