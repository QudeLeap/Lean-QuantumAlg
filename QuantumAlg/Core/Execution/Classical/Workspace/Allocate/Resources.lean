/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Induction
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Owned.CircuitRestoration

/-!
# Native bounds and borrowed restoration through heterogeneous allocation

Lexical classical allocation retains the body's actual path and native events.
Every borrowed resource is restored together with its external correlations
when the actual body restores that same complete interface in every scope.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit inner inner)

/-- An independent native budget for every actual body also bounds its lexical allocation. -/
theorem withCellsFrom_pool_le (budget : ResourcePool kind)
    (bodyBound : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (path : (body cells distinct innerTransport separated).Path),
      (body cells distinct innerTransport separated).resourcePool path ≤ budget)
    (path : (withCellsFrom transport shapes body).Path) :
    (withCellsFrom transport shapes body).resourcePool path ≤ budget := by
  have bound := withCellsFrom_property transport shapes body
    (fun _ code => ∀ selected : code.Path, code.resourcePool selected ≤ budget)
    (fun _ _ _ _ _ available => available) bodyBound
  exact bound path

/-- Workspace scopes retain the body's actual dependency depth under arbitrary native durations. -/
theorem withCellsFrom_depth_le (duration : Resource.Event kind → Nat) (budget : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (path : (body cells distinct innerTransport separated).Path),
      (body cells distinct innerTransport separated).depth duration path ≤ budget)
    (path : (withCellsFrom transport shapes body).Path) :
    (withCellsFrom transport shapes body).depth duration path ≤ budget := by
  have bound := withCellsFrom_property transport shapes body
    (fun _ code => ∀ selected : code.Path, code.depth duration selected ≤ budget)
    (fun _ _ _ _ _ available => available) bodyBound
  exact bound path

/-- Actual allocation and release preserve the body's complete borrowed-reference restoration. -/
theorem withCellsFrom_borrowedRestored (Reference : Register)
    (bodyRestores : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      {History : Type} [Fintype History] (state : State inner Reference History),
      (body cells distinct innerTransport separated).BorrowedRestored Reference state
        ((body cells distinct innerTransport separated).execute Reference state))
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (withCellsFrom transport shapes body).BorrowedRestored Reference state
      ((withCellsFrom transport shapes body).execute Reference state) := by
  have restores : ∀ {Past : Type} [Fintype Past] (initial : State ctx Reference Past),
      (withCellsFrom transport shapes body).BorrowedRestored Reference initial
        ((withCellsFrom transport shapes body).execute Reference initial) :=
    withCellsFrom_property transport shapes body
    (fun {inner} _ code => ∀ {History : Type} [Fintype History]
      (state : State inner Reference History),
      code.BorrowedRestored Reference state (code.execute Reference state))
    (fun _ key shape fresh code available =>
      Circuit.borrowedRestored_workspace key shape fresh code Reference available)
    bodyRestores
  exact restores state

end

end QuantumAlg.Execution.ClassicalWorkspace
