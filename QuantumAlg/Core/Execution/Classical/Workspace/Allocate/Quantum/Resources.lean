/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum.Induction
public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Execution.Owned.CircuitRestoration
public import QuantumAlg.Core.Execution.State
public import QuantumAlg.Core.Execution.Borrowed.State
public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum.Induction
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Owned.CircuitRestoration

/-! # Actual resources and borrowed restoration through physical-bank-preserving allocation -/

namespace QuantumAlg.Execution.ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} {outer ctx : RuntimeCtx model.kind}
    (transport : Transport outer ctx) (same : outer.quantumWires = ctx.quantumWires)
    (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
      outer.quantumWires = inner.quantumWires → Circuit model inner inner)

/-- The same actual body's native budget bounds the real classical allocation scopes. -/
public lemma withCellsWithQuantumWiresFrom_pool_le (budget : ResourcePool model)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires)
      (path : (body cells distinct innerTransport separated innerSame).Path),
      (body cells distinct innerTransport separated innerSame).resourcePool path ≤ budget)
    (path : (withCellsWithQuantumWiresFrom transport same shapes body).Path) :
    (withCellsWithQuantumWiresFrom transport same shapes body).resourcePool path ≤ budget := by
  have bound := withCellsWithQuantumWiresFrom_property transport same shapes body
    (fun _ _ code => ∀ selected : code.Path, code.resourcePool selected ≤ budget)
    (fun _ _ _ _ _ _ available => available) bodyBound
  exact bound path

/-- Native classical and quantum weights stay separate through the actual lexical scopes. -/
public lemma withCellsWithQuantumWiresFrom_weightedCount_le
    (weight : Resource.Event model → Nat) (budget : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires)
      (path : (body cells distinct innerTransport separated innerSame).Path),
      ResourcePool.weightedCount weight
        ((body cells distinct innerTransport separated innerSame).resourcePool path) ≤ budget)
    (path : (withCellsWithQuantumWiresFrom transport same shapes body).Path) :
    ResourcePool.weightedCount weight
      ((withCellsWithQuantumWiresFrom transport same shapes body).resourcePool path) ≤ budget := by
  have bound := withCellsWithQuantumWiresFrom_property transport same shapes body
    (fun _ _ code => ∀ selected : code.Path,
      ResourcePool.weightedCount weight (code.resourcePool selected) ≤ budget)
    (fun _ _ _ _ _ _ available => available) bodyBound
  exact bound path

/-- Every dependency depth is retained through the actual lexical classical scopes. -/
public lemma withCellsWithQuantumWiresFrom_depth_le
    (duration : Resource.Event model → Nat) (budget : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires)
      (path : (body cells distinct innerTransport separated innerSame).Path),
      (body cells distinct innerTransport separated innerSame).depth duration path ≤ budget)
    (path : (withCellsWithQuantumWiresFrom transport same shapes body).Path) :
    (withCellsWithQuantumWiresFrom transport same shapes body).depth duration path ≤ budget := by
  have bound := withCellsWithQuantumWiresFrom_property transport same shapes body
    (fun _ _ code => ∀ selected : code.Path, code.depth duration selected ≤ budget)
    (fun _ _ _ _ _ _ available => available) bodyBound
  exact bound path

/-- Scope release preserves complete borrowed input correlations when the actual body does. -/
public lemma withCellsWithQuantumWiresFrom_borrowedRestored (environment : model.Environment)
    (Reference : Register)
    (bodyRestores : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires)
      {History : Type} [Fintype History]
      (state : State inner Reference (model.HiddenState × History)),
      (body cells distinct innerTransport separated innerSame).BorrowedRestored Reference state
        ((body cells distinct innerTransport separated innerSame).execute environment Reference
          state))
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (withCellsWithQuantumWiresFrom transport same shapes body).BorrowedRestored Reference state
      ((withCellsWithQuantumWiresFrom transport same shapes body).execute environment Reference
        state) := by
  have restores : ∀ {Past : Type} [Fintype Past]
      (initial : State ctx Reference (model.HiddenState × Past)),
      (withCellsWithQuantumWiresFrom transport same shapes body).BorrowedRestored Reference initial
        ((withCellsWithQuantumWiresFrom transport same shapes body).execute environment Reference
          initial) :=
    withCellsWithQuantumWiresFrom_property transport same shapes body
      (fun {inner} _ _ code => ∀ {History : Type} [Fintype History]
        (state : State inner Reference (model.HiddenState × History)),
        code.BorrowedRestored Reference state (code.execute environment Reference state))
      (fun _ _ key shape fresh code available =>
        Circuit.borrowedRestored_workspace (environment := environment)
          key shape fresh code Reference available)
      bodyRestores
  exact restores state

end

end QuantumAlg.Execution.ClassicalWorkspace
