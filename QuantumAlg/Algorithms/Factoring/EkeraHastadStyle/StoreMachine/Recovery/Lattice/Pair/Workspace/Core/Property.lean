/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Core
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Induction

/-!
# Compositional properties of the actual core allocator

A property preserved by lexical workspace scopes lifts from every actual body
through the shared, slot and state packages, with their generated certificates.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace

open Execution.ClassicalWorkspace

/-- Lift a property through all three actual core packages and their physical certificates. -/
lemma withWorkspaces_property {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (N : Nat)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner), Certificates transport cells → Circuit model inner inner)
    (property : ∀ {inner : RuntimeCtx model.kind}, Circuit model inner inner → Prop)
    (workspaceProperty : ∀ (inner : RuntimeCtx model.kind) (key : StorageKey) (shape : CShape)
      (fresh : key ∉ inner.keys)
      (code : Circuit model (inner.addWorkspace key shape fresh)
        (inner.addWorkspace key shape fresh)),
      property code → property (Circuit.workspace inner key shape fresh code))
    (bodyProperty : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells),
      property (body cells transport certificates)) :
    property (withWorkspaces ctx N body) := by
  unfold withWorkspaces
  apply withCellsFrom_property _ _ _ (fun _ code => property code)
    (fun _ key shape fresh code available => workspaceProperty _ key shape fresh code available)
  intro sharedCtx shared sharedDistinct rootTransport sharedSeparated
  apply withCellsFrom_property _ _ _ (fun _ code => property code)
    (fun _ key shape fresh code available => workspaceProperty _ key shape fresh code available)
  intro slotCtx slot slotDistinct slotTransport slotSeparated
  apply withCellsFrom_property _ _ _ (fun _ code => property code)
    (fun _ key shape fresh code available => workspaceProperty _ key shape fresh code available)
  intro stateCtx state stateDistinct stateTransport stateSeparated
  exact bodyProperty _ _ _

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace
