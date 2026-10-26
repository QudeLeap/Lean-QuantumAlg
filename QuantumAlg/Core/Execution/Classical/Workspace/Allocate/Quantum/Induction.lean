/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum

/-! # Composition through actual classical allocation with retained quantum wires -/

namespace QuantumAlg.Execution.ClassicalWorkspace

/-- Lift a body property through the actual lexical scopes and their physical-wire equalities. -/
public lemma withCellsWithQuantumWiresFrom_property {model : ExecutionModel}
    {outer ctx : RuntimeCtx model.kind} (transport : Transport outer ctx)
    (same : outer.quantumWires = ctx.quantumWires) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
      outer.quantumWires = inner.quantumWires → Circuit model inner inner)
    (property : ∀ {inner : RuntimeCtx model.kind}, Transport outer inner →
      outer.quantumWires = inner.quantumWires → Circuit model inner inner → Prop)
    (workspaceProperty : ∀ {inner : RuntimeCtx model.kind} (innerTransport : Transport outer inner)
      (innerSame : outer.quantumWires = inner.quantumWires)
      (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
      (code : Circuit model (inner.addWorkspace key shape fresh)
        (inner.addWorkspace key shape fresh)),
      property (innerTransport.underWorkspace key shape fresh)
        (quantumWires_same_underWorkspace innerSame key shape fresh) code →
          property innerTransport innerSame (Circuit.workspace inner key shape fresh code))
    (bodyProperty : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires),
      property innerTransport innerSame (body cells distinct innerTransport separated innerSame)) :
    property transport same (withCellsWithQuantumWiresFrom transport same shapes body) := by
  induction shapes generalizing ctx with
  | nil => exact bodyProperty _ _ _ _ _
  | cons shape shapes inductionHypothesis =>
      dsimp only [withCellsWithQuantumWiresFrom]
      apply inductionHypothesis
      intro inner cells distinct innerTransport separated innerSame
      apply workspaceProperty
      exact bodyProperty _ _ _ _ _

end QuantumAlg.Execution.ClassicalWorkspace
