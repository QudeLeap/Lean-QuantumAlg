/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Separation
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Transport

/-!
# Live heterogeneous workspace packages across nested lexical scopes

Packages carry physical cell distinctness and separation from the complete
storage support of caller reads. Further structural transport preserves both
properties, and fresh allocation separates old packages from new packages.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

/-- Indexed lookup commutes with transport of a heterogeneous package. -/
theorem workspaceCells_cellAt_transportCells_ref {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} {shapes : List CShape}
    (transport : Transport outer inner) (cells : Cells outer shapes)
    (index : Fin shapes.length) :
    (cellAt (transportCells transport cells) index).ref =
      transport.liftWrite (cellAt cells index).ref := by
  induction cells with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · exact inductionHypothesis tailIndex

/-- A transported package stays separate from all reads of the original caller. -/
theorem workspaceCells_transportCells_transportSeparated {kind : ProblemKind}
    {outer middle inner : RuntimeCtx kind} {shapes : List CShape}
    (outerTransport : Transport outer middle)
    (innerTransport : Transport middle inner) (cells : Cells middle shapes)
    (separated : cells.TransportSeparated outerTransport) :
    (transportCells innerTransport cells).TransportSeparated
      (outerTransport.compose innerTransport) := by
  induction cells with
  | nil => trivial
  | cons head tail inductionHypothesis =>
      refine ⟨?_, inductionHypothesis separated.2⟩
      intro shape input
      rw [Transport.liftInput_compose]
      change (innerTransport.liftWrite head.ref).key ∉
        (innerTransport.liftInput (outerTransport.liftInput input)).storageKeys
      rw [innerTransport.liftWrite_key, innerTransport.liftInput_storageKeys]
      exact separated.1 input

/-- Separation from an immediate caller also covers every earlier caller read. -/
theorem workspaceCells_transportSeparated_compose {kind : ProblemKind}
    {outer middle inner : RuntimeCtx kind} {shapes : List CShape}
    (outerTransport : Transport outer middle)
    (innerTransport : Transport middle inner) (cells : Cells inner shapes)
    (separated : cells.TransportSeparated innerTransport) :
    cells.TransportSeparated (outerTransport.compose innerTransport) := by
  induction cells with
  | nil => trivial
  | cons head tail inductionHypothesis =>
      refine ⟨?_, inductionHypothesis separated.2⟩
      intro shape input
      rw [Transport.liftInput_compose]
      exact separated.1 (outerTransport.liftInput input)

/-- One live package with physical distinctness and complete caller-read separation. -/
structure Live {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    (transport : Transport outer ctx) (shapes : List CShape) where
  cells : Cells ctx shapes
  distinct : cells.Distinct
  separated : cells.TransportSeparated transport

/-- Transport one live package through a further lexical scope. -/
def Live.transport {kind : ProblemKind}
    {outer middle inner : RuntimeCtx kind} {shapes : List CShape}
    {outerTransport : Transport outer middle} (package : Live outerTransport shapes)
    (innerTransport : Transport middle inner) :
    Live (outerTransport.compose innerTransport) shapes where
  cells := transportCells innerTransport package.cells
  distinct := workspaceCells_transportCells_distinct innerTransport
    package.cells package.distinct
  separated := workspaceCells_transportCells_transportSeparated
    outerTransport innerTransport package.cells package.separated

/-- Package fresh cells beneath a scope reached from an earlier caller. -/
def Live.ofFresh {kind : ProblemKind}
    {outer middle inner : RuntimeCtx kind} {shapes : List CShape}
    (outerTransport : Transport outer middle) (innerTransport : Transport middle inner)
    (cells : Cells inner shapes) (distinct : cells.Distinct)
    (separated : cells.TransportSeparated innerTransport) :
    Live (outerTransport.compose innerTransport) shapes where
  cells := cells
  distinct := distinct
  separated := workspaceCells_transportSeparated_compose
    outerTransport innerTransport cells separated

/-- Every cell of one package has a different physical key from every cell of another. -/
structure CrossSeparated {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {leftShapes rightShapes : List CShape}
    (left : Cells ctx leftShapes) (right : Cells ctx rightShapes) : Prop where
  keysNe : ∀ (leftIndex : Fin leftShapes.length) (rightIndex : Fin rightShapes.length),
    (cellAt left leftIndex).ref.key ≠ (cellAt right rightIndex).ref.key

/-- Physical cross-package separation is symmetric. -/
theorem CrossSeparated.symm {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {leftShapes rightShapes : List CShape}
    {left : Cells ctx leftShapes} {right : Cells ctx rightShapes}
    (separated : CrossSeparated left right) : CrossSeparated right left := by
  exact ⟨fun rightIndex leftIndex => (separated.keysNe leftIndex rightIndex).symm⟩

/-- Cross-package separation survives a further structural scope transport. -/
theorem CrossSeparated.transport {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} {leftShapes rightShapes : List CShape}
    {left : Cells outer leftShapes} {right : Cells outer rightShapes}
    (separated : CrossSeparated left right) (transport : Transport outer inner) :
    CrossSeparated (transportCells transport left) (transportCells transport right) := by
  refine ⟨?_⟩
  intro leftIndex rightIndex
  rw [workspaceCells_cellAt_transportCells_ref, workspaceCells_cellAt_transportCells_ref,
    transport.liftWrite_key, transport.liftWrite_key]
  exact separated.keysNe leftIndex rightIndex

/-- Caller-read separation of fresh cells separates them from every transported live cell. -/
theorem crossSeparated_of_nested {kind : ProblemKind}
    {middle inner : RuntimeCtx kind} {leftShapes rightShapes : List CShape}
    (transport : Transport middle inner) (left : Cells middle leftShapes)
    (right : Cells inner rightShapes) (separated : right.TransportSeparated transport) :
    CrossSeparated (transportCells transport left) right := by
  refine ⟨?_⟩
  intro leftIndex rightIndex
  have avoids := Cells.workspaceCells_cellAt_transport_avoids right transport separated
    (.storage (cellAt left leftIndex).ref.toCStorageRef) rightIndex
  rw [transport.liftInput_storageKeys] at avoids
  have keysNe : (cellAt right rightIndex).ref.key ≠ (cellAt left leftIndex).ref.key := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using avoids
  rw [workspaceCells_cellAt_transportCells_ref, transport.liftWrite_key]
  exact keysNe.symm

end QuantumAlg.Execution.ClassicalWorkspace
