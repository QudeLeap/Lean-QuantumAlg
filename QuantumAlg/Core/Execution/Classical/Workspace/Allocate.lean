/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Freshness
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Separation
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Transport

/-!
# Heterogeneous allocation through the existing Circuit workspace instruction

The deepest continuation receives actual typed cells, their distinctness,
structural caller references and complete separation from caller read support.
The returned program is composed solely of the existing lexical instruction.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

/-- Allocate a heterogeneous list beneath an existing lexical transport.

The list head is allocated deepest, so the final `Cells` order is
definitionally the order of `shapes`. -/
def withCellsFrom {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} (transport : Transport outer ctx) :
    (shapes : List CShape) →
      (body : ∀ {inner : RuntimeCtx kind}
        (cells : Cells inner shapes), cells.Distinct →
        (innerTransport : Transport outer inner) →
        cells.TransportSeparated innerTransport →
          Circuit inner inner) →
        Circuit ctx ctx
  | [], body =>
      body Cells.nil (by trivial) transport
        (Cells.workspaceCells_transportSeparated_nil transport)
  | shape :: shapes, body =>
      withCellsFrom transport shapes fun
          {inner} cells cellsDistinct innerTransport cellsSeparated =>
        let key := inner.canonicalFreshKey
        let fresh : key ∉ inner.keys := inner.canonicalFreshKey_fresh
        Circuit.workspace inner key shape fresh <|
          let output := CWriteRef.workspaceHead inner key shape fresh
          let outputRole : output.toCStorageRef.role = .workspace := rfl
          let liftedCells := cells.underWorkspace key shape fresh
          let newCell : Cell
              (inner.addWorkspace key shape fresh) shape :=
            { ref := output, role := outputRole }
          let allCells := Cells.cons newCell liftedCells
          have liftedDistinct : liftedCells.Distinct :=
            Cells.workspaceCells_underWorkspace_distinct cells cellsDistinct
              key shape fresh
          have liftedAvoids :
              liftedCells.AvoidsKey newCell.ref.toCStorageRef.key := by
            simp only [newCell, output, CWriteRef.workspaceHead,
              CStorageRef.workspaceHead]
            exact Cells.workspaceCells_underWorkspace_avoids_fresh
              cells key shape fresh
          have allDistinct : allCells.Distinct :=
            Cells.workspaceCells_cons_distinct newCell liftedCells liftedAvoids
              liftedDistinct
          have allSeparated : allCells.TransportSeparated
              (innerTransport.underWorkspace key shape fresh) := by
            exact Cells.workspaceCells_transportSeparated_extend cells
              innerTransport key shape fresh cellsSeparated
          body allCells allDistinct
            (innerTransport.underWorkspace key shape fresh) allSeparated

/-- Allocate a heterogeneous list directly beneath one caller context. -/
def withCells {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx kind}
      (cells : Cells inner shapes), cells.Distinct →
      (transport : Transport ctx inner) →
      cells.TransportSeparated transport →
        Circuit inner inner) : Circuit ctx ctx :=
  withCellsFrom (Transport.id ctx) shapes body


end QuantumAlg.Execution.ClassicalWorkspace
