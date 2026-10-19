/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Induction over actual heterogeneous lexical allocation

A property of the actual body extends through the allocator whenever the same
property is preserved by the existing workspace instruction. The transport in
the motive exposes exactly the caller references available in each scope.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

/-- Lift a body property through the allocator's actual nested workspace instructions. -/
lemma withCellsFrom_property {model : ExecutionModel}
    {outer ctx : RuntimeCtx model.kind} (transport : Transport outer ctx)
    (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit model inner inner)
    (property : ∀ {inner : RuntimeCtx model.kind}, Transport outer inner →
      Circuit model inner inner → Prop)
    (workspaceProperty : ∀ {inner : RuntimeCtx model.kind} (innerTransport : Transport outer inner)
      (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
      (code : Circuit model (inner.addWorkspace key shape fresh)
        (inner.addWorkspace key shape fresh)),
      property (innerTransport.underWorkspace key shape fresh) code →
        property innerTransport (Circuit.workspace inner key shape fresh code))
    (bodyProperty : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport),
      property innerTransport (body cells distinct innerTransport separated)) :
    property transport (withCellsFrom transport shapes body) := by
  induction shapes generalizing ctx with
  | nil => exact bodyProperty _ _ _ _
  | cons shape shapes inductionHypothesis =>
      dsimp only [withCellsFrom]
      apply inductionHypothesis
      intro inner cells distinct innerTransport separated
      apply workspaceProperty
      exact bodyProperty _ _ _ _

end QuantumAlg.Execution.ClassicalWorkspace
