/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace

/-!
# Independent budgets for the actual complete batch allocation

The native trace and dependency depth are those of the actual callback. Space
counts the six persistent cells, all six pair packages, and the independent
quadratic package jointly, before adding any callback allocation budget.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspace

open Execution
open Execution.ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (N : Nat)
    (body : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N), top.Distinct →
      (topTransport : Transport ctx topCtx) → top.TransportSeparated topTransport →
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N) →
      (pairTransport : Transport topCtx inner) →
      LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells →
        Circuit model inner inner)

/-- Lift one compositional property through all eight actually nested cell packages. -/
theorem withWorkspaces_property
    (property : ∀ {inner : RuntimeCtx model.kind}, Circuit model inner inner → Prop)
    (workspaceProperty : ∀ (inner : RuntimeCtx model.kind) (key : StorageKey) (shape : CShape)
      (fresh : key ∉ inner.keys)
      (code : Circuit model (inner.addWorkspace key shape fresh)
        (inner.addWorkspace key shape fresh)),
      property code → property (Circuit.workspace inner key shape fresh code))
    (bodyProperty : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
      (topDistinct : top.Distinct) (topTransport : Transport ctx topCtx)
      (topSeparated : top.TransportSeparated topTransport)
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
      (pairTransport : Transport topCtx inner)
      (certificates : LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells),
      property (body top topDistinct topTransport topSeparated cells pairTransport certificates)) :
    property (withWorkspaces ctx N body) := by
  unfold withWorkspaces
  apply withCellsFrom_property _ _ _ (fun _ code => property code)
    (fun _ key shape fresh code available => workspaceProperty _ key shape fresh code available)
  intro topCtx top topDistinct topTransport topSeparated
  apply LatticePairRecoveryWorkspace.withWorkspaces_property _ _ _ property workspaceProperty
  intro pairCtx pair pairTransport pairCertificates
  apply withCellsFrom_property _ _ _ (fun _ code => property code)
    (fun _ key shape fresh code available => workspaceProperty _ key shape fresh code available)
  intro inner quadratic quadraticDistinct quadraticTransport quadraticSeparated
  exact bodyProperty _ _ _ _ _ _ _

/-- Native coordinates follow the same actual callback path. -/
theorem withWorkspaces_pool_le (budget : ResourcePool model)
    (bodyBound : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
      (topDistinct : top.Distinct) (topTransport : Transport ctx topCtx)
      (topSeparated : top.TransportSeparated topTransport)
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
      (pairTransport : Transport topCtx inner)
      (certificates : LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells)
      (path :
        (body top topDistinct topTransport topSeparated cells pairTransport certificates).Path),
      (body top topDistinct topTransport topSeparated cells pairTransport certificates).resourcePool
        path ≤ budget)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).resourcePool path ≤ budget := by
  have bound := withWorkspaces_property ctx N body
    (fun code => ∀ selected : code.Path, code.resourcePool selected ≤ budget)
    (fun _ _ _ _ _ available => available) bodyBound
  exact bound path

/-- Actual dependency depth retains the independent callback budget. -/
theorem withWorkspaces_depth_le (duration : Resource.Event model → Nat) (budget : Nat)
    (bodyBound : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
      (topDistinct : top.Distinct) (topTransport : Transport ctx topCtx)
      (topSeparated : top.TransportSeparated topTransport)
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
      (pairTransport : Transport topCtx inner)
      (certificates : LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells)
      (path :
        (body top topDistinct topTransport topSeparated cells pairTransport certificates).Path),
      (body top topDistinct topTransport topSeparated cells pairTransport certificates).depth
        duration path ≤ budget)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).depth duration path ≤ budget := by
  have bound := withWorkspaces_property ctx N body
    (fun code => ∀ selected : code.Path, code.depth duration selected ≤ budget)
    (fun _ _ _ _ _ available => available) bodyBound
  exact bound path

/-- Complete borrowed resources retain their external-reference correlations after release. -/
theorem withWorkspaces_borrowedRestored (Reference : Register)
    (bodyRestores : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
      (topDistinct : top.Distinct) (topTransport : Transport ctx topCtx)
      (topSeparated : top.TransportSeparated topTransport)
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
      (pairTransport : Transport topCtx inner)
      (certificates : LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells)
      {History : Type} [Fintype History]
      (state : State inner Reference (model.HiddenState × History)),
      (body top topDistinct topTransport topSeparated cells pairTransport
        certificates).BorrowedRestored
        Reference
        state
        ((body top topDistinct topTransport topSeparated cells pairTransport certificates).execute
          Reference state))
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (withWorkspaces ctx N body).BorrowedRestored Reference state
      ((withWorkspaces ctx N body).execute Reference state) := by
  have restores : ∀ {Past : Type} [Fintype Past]
      (initial : State ctx Reference (model.HiddenState × Past)),
      (withWorkspaces ctx N body).BorrowedRestored Reference initial
        ((withWorkspaces ctx N body).execute Reference initial) :=
    withWorkspaces_property ctx N body
      (fun {inner} code => ∀ {Past : Type} [Fintype Past]
        (initial : State inner Reference (model.HiddenState × Past)),
        code.BorrowedRestored Reference initial (code.execute Reference initial))
      (fun _ key shape fresh code available =>
        Circuit.borrowedRestored_workspace key shape fresh code Reference available)
      bodyRestores
  exact restores state

/-- Independent sum of every shape list allocated around the actual batch callback. -/
def allocationSpace {kind : ProblemKind} : SpacePool kind :=
  ((LatticeBatchRecoveryWorkspaceLayout.topShapes N).map SpacePool.ofShape).sum +
    LatticePairRecoveryWorkspace.allocationSpace N +
    ((QuadraticScratchLayout.shapes N).map SpacePool.ofShape).sum

/-- The actual resident peak charges every simultaneously live allocation once. -/
theorem withWorkspaces_resident_le (additional : SpacePool model.kind)
    (bodyBound : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
      (topDistinct : top.Distinct) (topTransport : Transport ctx topCtx)
      (topSeparated : top.TransportSeparated topTransport)
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
      (pairTransport : Transport topCtx inner)
      (certificates : LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells)
      (path :
        (body top topDistinct topTransport topSeparated cells pairTransport certificates).Path),
      (body top topDistinct topTransport topSeparated cells pairTransport
        certificates).peakResidentSpace
        path ≤
        additional + inner.residentSpace)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).peakResidentSpace
        path ≤
      allocationSpace N + additional + ctx.residentSpace := by
  let quadraticSpace : SpacePool model.kind :=
    ((QuadraticScratchLayout.shapes N).map SpacePool.ofShape).sum
  unfold withWorkspaces at path ⊢
  refine (withCellsFrom_resident_le _ _ _
    (LatticePairRecoveryWorkspace.allocationSpace N + (quadraticSpace + additional))
    ?_ path).trans ?_
  · intro topCtx top topDistinct topTransport topSeparated topPath
    apply LatticePairRecoveryWorkspace.withWorkspaces_resident_le _ _ _
      (quadraticSpace + additional) ?_ topPath
    intro pairCtx pair pairTransport pairCertificates pairPath
    apply withCellsFrom_resident_le _ _ _ additional ?_ pairPath
    intro inner quadratic quadraticDistinct quadraticTransport quadraticSeparated innerPath
    exact bodyBound _ _ _ _ _ _ _ innerPath
  · exact le_of_eq (by simp only [allocationSpace, quadraticSpace, add_assoc])

/-- The actual auxiliary peak charges every simultaneously live allocation once. -/
theorem withWorkspaces_auxiliary_le (additional : SpacePool model.kind)
    (bodyBound : ∀ {topCtx inner : RuntimeCtx model.kind}
      (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
      (topDistinct : top.Distinct) (topTransport : Transport ctx topCtx)
      (topSeparated : top.TransportSeparated topTransport)
      (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
      (pairTransport : Transport topCtx inner)
      (certificates : LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells)
      (path :
        (body top topDistinct topTransport topSeparated cells pairTransport certificates).Path),
      (body top topDistinct topTransport topSeparated cells pairTransport
        certificates).peakAuxiliarySpace
        path ≤
        additional + inner.auxiliarySpace)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).peakAuxiliarySpace
        path ≤
      allocationSpace N + additional + ctx.auxiliarySpace := by
  let quadraticSpace : SpacePool model.kind :=
    ((QuadraticScratchLayout.shapes N).map SpacePool.ofShape).sum
  unfold withWorkspaces at path ⊢
  refine (withCellsFrom_auxiliary_le _ _ _
    (LatticePairRecoveryWorkspace.allocationSpace N + (quadraticSpace + additional))
    ?_ path).trans ?_
  · intro topCtx top topDistinct topTransport topSeparated topPath
    apply LatticePairRecoveryWorkspace.withWorkspaces_auxiliary_le _ _ _
      (quadraticSpace + additional) ?_ topPath
    intro pairCtx pair pairTransport pairCertificates pairPath
    apply withCellsFrom_auxiliary_le _ _ _ additional ?_ pairPath
    intro inner quadratic quadraticDistinct quadraticTransport quadraticSeparated innerPath
    exact bodyBound _ _ _ _ _ _ _ innerPath
  · exact le_of_eq (by simp only [allocationSpace, quadraticSpace, add_assoc])

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspace
