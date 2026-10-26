/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Allocate
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Classical allocation with the original complete quantum wire record

The actual nested classical workspace instructions retain every original
quantum wire in order. Their continuation receives this proved equality
beside the same typed storage transport and fresh-cell separation. The
equality cannot be inferred from a storage transport alone.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

/-- Extending only classical storage retains the complete physical quantum bank. -/
public lemma quantumWires_same_underWorkspace {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (same : outer.quantumWires = inner.quantumWires)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys) :
    outer.quantumWires = (inner.addWorkspace key shape fresh).quantumWires :=
  same.trans (RuntimeCtx.quantumWires_addWorkspace inner key shape fresh).symm

/-- Allocate actual classical cells while retaining the complete original physical quantum bank. -/
public def withCellsWithQuantumWiresFrom {model : ExecutionModel}
    {outer ctx : RuntimeCtx model.kind} (transport : Transport outer ctx)
    (same : outer.quantumWires = ctx.quantumWires) :
    (shapes : List CShape) →
      (body : ∀ {inner : RuntimeCtx model.kind}
        (cells : Cells inner shapes), cells.Distinct →
        (innerTransport : Transport outer inner) →
        cells.TransportSeparated innerTransport →
        outer.quantumWires = inner.quantumWires → Circuit model inner inner) →
          Circuit model ctx ctx
  | [], body =>
      body Cells.nil (by trivial) transport
        (Cells.workspaceCells_transportSeparated_nil transport) same
  | shape :: shapes, body =>
      withCellsWithQuantumWiresFrom transport same shapes fun
          {inner} cells cellsDistinct innerTransport cellsSeparated innerSame =>
        let key := inner.canonicalFreshKey
        let fresh : key ∉ inner.keys := inner.canonicalFreshKey_fresh
        Circuit.workspace inner key shape fresh <|
          let output := CWriteRef.workspaceHead inner key shape fresh
          let outputRole : output.toCStorageRef.role = .workspace := rfl
          let liftedCells := cells.underWorkspace key shape fresh
          let newCell : Cell (inner.addWorkspace key shape fresh) shape :=
            { ref := output, role := outputRole }
          let allCells := Cells.cons newCell liftedCells
          have liftedDistinct : liftedCells.Distinct :=
            Cells.workspaceCells_underWorkspace_distinct cells cellsDistinct key shape fresh
          have liftedAvoids : liftedCells.AvoidsKey newCell.ref.toCStorageRef.key := by
            simp only [newCell, output, CWriteRef.workspaceHead, CStorageRef.workspaceHead]
            exact Cells.workspaceCells_underWorkspace_avoids_fresh cells key shape fresh
          have allDistinct : allCells.Distinct :=
            Cells.workspaceCells_cons_distinct newCell liftedCells liftedAvoids liftedDistinct
          have allSeparated : allCells.TransportSeparated
              (innerTransport.underWorkspace key shape fresh) := by
            exact Cells.workspaceCells_transportSeparated_extend cells innerTransport
              key shape fresh cellsSeparated
          have retained : outer.quantumWires =
              (inner.addWorkspace key shape fresh).quantumWires :=
            quantumWires_same_underWorkspace innerSame key shape fresh
          body allCells allDistinct (innerTransport.underWorkspace key shape fresh)
            allSeparated retained

/-- The original storage identity and physical quantum bank are the allocator's initial data. -/
public def withCellsWithQuantumWires {model : ExecutionModel} (ctx : RuntimeCtx model.kind)
    (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind}
      (cells : Cells inner shapes), cells.Distinct →
      (transport : Transport ctx inner) → cells.TransportSeparated transport →
      ctx.quantumWires = inner.quantumWires → Circuit model inner inner) : Circuit model ctx ctx :=
  withCellsWithQuantumWiresFrom (Transport.id ctx) rfl shapes body

/-- The same full ordered quantum wire record supplies the typed physical-layout equality. -/
public lemma quantumLayout_wires_of_quantumWires {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (same : outer.quantumWires = inner.quantumWires) :
    outer.quantumLayout.wires = inner.quantumLayout.wires :=
  outer.quantumLayout_wires.trans (same.trans inner.quantumLayout_wires.symm)

end QuantumAlg.Execution.ClassicalWorkspace
