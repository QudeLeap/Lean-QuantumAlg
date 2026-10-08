/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace

/-!
# Initialized actual allocation of the complete batch workspace

The same actual interpreter record supplies canonical initial values for the
persistent top cells, all six pair packages and the independent quadratic
package. The body writes the caller-visible output before these scopes pop;
the caller postcondition is evaluated on restriction of those actual stores.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspace

open Execution
open Execution.ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Initialization of the seven live scratch packages, supplied by their actual allocation. -/
structure Initialized {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (store : Store ctx) (cells : LatticePairFactorWorkspaceSeparation.Cells ctx N) : Prop where
  pair : LatticePairRecoveryWorkspace.Initialized store cells.pair
  quadratic : cells.quadratic.Initialized store

/-- Actual allocation supplies every entry value and returns the complete caller postcondition. -/
theorem withWorkspaces_actualRecord_initialized_post {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (N : Nat)
    (body : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N), top.Distinct →
      (topTransport : Transport ctx topCtx) → top.TransportSeparated topTransport →
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N) →
      (pairTransport : Transport topCtx inner) →
      LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells →
        Circuit model inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (bodyContract : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
      (topDistinct : top.Distinct) (topTransport : Transport ctx topCtx)
      (topSeparated : top.TransportSeparated topTransport)
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
      (pairTransport : Transport topCtx inner)
      (certificates : LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells),
      ∃ step : Store inner → Store inner ×
          (body top topDistinct topTransport topSeparated cells pairTransport certificates).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference (model.HiddenState × History)),
          (body top topDistinct topTransport topSeparated cells pairTransport certificates).execute
              Reference state = state.mapClassical (fun entry =>
                ((step entry.1).1, (entry.2.1, (entry.2.2, (step entry.1).2))))) ∧
        ∀ before : Store inner, (transportCells pairTransport top).Initialized before →
          Initialized before cells →
          Post ((topTransport.compose pairTransport).restrict before)
            ((topTransport.compose pairTransport).restrict (step before).1)) :
    ∃ step : Store ctx → Store ctx × (withWorkspaces ctx N body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withWorkspaces ctx N body).execute Reference state = state.mapClassical (fun entry =>
          ((step entry.1).1, (entry.2.1, (entry.2.2, (step entry.1).2))))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  unfold withWorkspaces
  apply withCells_actualStoreRecord_initialized_restricted_post _ _ _ Post
  intro topCtx top topDistinct topTransport topSeparated
  apply LatticePairRecoveryWorkspace.withWorkspaces_actualRecord_initialized_post _ _ _
    (fun before after => top.Initialized before →
      Post (topTransport.restrict before) (topTransport.restrict after))
  intro pairCtx pair pairTransport pairCertificates
  apply withCells_actualStoreRecord_initialized_restricted_post _ _ _
    (fun before after => LatticePairRecoveryWorkspace.Initialized before pair →
      top.Initialized (pairTransport.restrict before) →
      Post (topTransport.restrict (pairTransport.restrict before))
        (topTransport.restrict (pairTransport.restrict after)))
  intro inner quadratic quadraticDistinct quadraticTransport quadraticSeparated
  refine Exists.imp ?_ (bodyContract _ _ _ _ _ _ _)
  intro step contract
  obtain ⟨equation, correct⟩ := contract
  refine ⟨equation, ?_⟩
  intro before quadraticInitial pairInitial topInitial
  have pairAt := pairInitial.transport quadraticTransport
    (quadraticTransport.workspaceTransport_restrict_readsAs before)
  have topSource :
      top.Initialized ((pairTransport.compose quadraticTransport).restrict before) := by
    simpa only [Transport.workspaceTransport_restrict_compose] using topInitial
  have transported := Cells.workspaceCells_initialized_transport
    (pairTransport.compose quadraticTransport) top
    ((pairTransport.compose quadraticTransport).workspaceTransport_restrict_readsAs before)
    topSource
  simpa only [Transport.workspaceTransport_restrict_compose] using
    correct before transported ⟨pairAt, quadraticInitial⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspace
