/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Allocate
public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Execution.Owned.CircuitRestoration
public import QuantumAlg.Core.Execution.State
public import QuantumAlg.Core.Execution.Borrowed.State
public import QuantumAlg.Core.Execution.Interpret
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

variable {model : ExecutionModel} {outer ctx : RuntimeCtx model.kind}
    (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit model inner inner)

/-- An independent native budget for every actual body also bounds its lexical allocation. -/
public lemma withCellsFrom_pool_le (budget : ResourcePool model)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
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
public lemma withCellsFrom_depth_le (duration : Resource.Event model → Nat) (budget : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
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
public lemma withCellsFrom_borrowedRestored (environment : model.Environment)
    (Reference : Register)
    (bodyRestores : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      {History : Type} [Fintype History]
      (state : State inner Reference (model.HiddenState × History)),
      (body cells distinct innerTransport separated).BorrowedRestored Reference state
        ((body cells distinct innerTransport separated).execute environment Reference state))
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (withCellsFrom transport shapes body).BorrowedRestored Reference state
      ((withCellsFrom transport shapes body).execute environment Reference state) := by
  have restores : ∀ {Past : Type} [Fintype Past]
      (initial : State ctx Reference (model.HiddenState × Past)),
      (withCellsFrom transport shapes body).BorrowedRestored Reference initial
        ((withCellsFrom transport shapes body).execute environment Reference initial) :=
    withCellsFrom_property transport shapes body
    (fun {inner} _ code => ∀ {History : Type} [Fintype History]
      (state : State inner Reference (model.HiddenState × History)),
      code.BorrowedRestored Reference state (code.execute environment Reference state))
    (fun _ key shape fresh code available =>
      Circuit.borrowedRestored_workspace (environment := environment)
        key shape fresh code Reference available)
    bodyRestores
  exact restores state

end

end QuantumAlg.Execution.ClassicalWorkspace
