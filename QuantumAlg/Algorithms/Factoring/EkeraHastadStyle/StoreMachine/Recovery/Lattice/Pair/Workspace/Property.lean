/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Core.Property

/-!
# Compositional properties of all actual pair-recovery packages
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace

open Execution.ClassicalWorkspace

/-- Lift a body property through the six packages actually allocated by pair recovery. -/
theorem withWorkspaces_property {model : ExecutionModel}
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
  apply LatticePairCoreWorkspace.withWorkspaces_property _ _ _ property workspaceProperty
  intro coreCtx core coreTransport coreCertificates
  apply withCellsFrom_property _ _ _ (fun _ code => property code)
    (fun _ key shape fresh code available => workspaceProperty _ key shape fresh code available)
  intro targetCtx target targetDistinct targetTransport targetSeparated
  apply withCellsFrom_property _ _ _ (fun _ code => property code)
    (fun _ key shape fresh code available => workspaceProperty _ key shape fresh code available)
  intro lllCtx lll lllDistinct lllTransport lllSeparated
  apply withCellsFrom_property _ _ _ (fun _ code => property code)
    (fun _ key shape fresh code available => workspaceProperty _ key shape fresh code available)
  intro nearestCtx nearest nearestDistinct nearestTransport nearestSeparated
  exact bodyProperty _ _ _

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace
