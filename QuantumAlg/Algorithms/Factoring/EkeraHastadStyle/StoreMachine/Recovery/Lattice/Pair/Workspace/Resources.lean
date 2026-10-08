/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Property
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Owned.CircuitRestoration

/-!
# Native budgets and joint restoration through actual pair allocation

Independent bounds for the body cover the same actual path through all six
lexical packages. Borrowed restoration includes its complete classical,
quantum and external-reference correlations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace

open Execution
open Execution.ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (N : Nat)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner), Certificates transport cells → Circuit model inner inner)

/-- Allocation retains the independent native coordinate bound of its actual body. -/
theorem withWorkspaces_pool_le (budget : ResourcePool model)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells)
      (path : (body cells transport certificates).Path),
      (body cells transport certificates).resourcePool path ≤ budget)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).resourcePool path ≤ budget := by
  have bound := withWorkspaces_property ctx N body
    (fun code => ∀ selected : code.Path, code.resourcePool selected ≤ budget)
    (fun _ _ _ _ _ available => available) bodyBound
  exact bound path

/-- Every actual dependency depth meets the same independent body bound. -/
theorem withWorkspaces_depth_le (duration : Resource.Event model → Nat) (budget : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells)
      (path : (body cells transport certificates).Path),
      (body cells transport certificates).depth duration path ≤ budget)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).depth duration path ≤ budget := by
  have bound := withWorkspaces_property ctx N body
    (fun code => ∀ selected : code.Path, code.depth duration selected ≤ budget)
    (fun _ _ _ _ _ available => available) bodyBound
  exact bound path

/-- The six actual scopes preserve complete borrowed-reference restoration of every body. -/
theorem withWorkspaces_borrowedRestored (Reference : Register)
    (bodyRestores : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells)
      {History : Type} [Fintype History]
      (state : State inner Reference (model.HiddenState × History)),
      (body cells transport certificates).BorrowedRestored Reference state
        ((body cells transport certificates).execute Reference state))
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

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace
