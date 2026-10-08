/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
public import QuantumAlg.Core.Execution.Classical.Workspace.Transport
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport

/-!
# Exact caller-read separation from actual lexical workspace cells
-/

namespace QuantumAlg.Execution.ClassicalWorkspace.Cells

/-- Every caller read remains separate from every allocated workspace cell. -/
public def TransportSeparated {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes)
    (transport : Transport outer ctx) : Prop :=
  match cells with
  | .nil => True
  | .cons head tail =>
      (∀ {shape : CShape} (input : CInputRef outer shape),
        head.ref.key ∉ (transport.liftInput input).storageKeys) ∧
      tail.TransportSeparated transport

public theorem workspaceCells_transportSeparated_nil {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} (transport : Transport outer ctx) :
    TransportSeparated (.nil : Cells ctx []) transport := by trivial

public theorem workspaceCells_transportSeparated_underWorkspace {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (transport : Transport outer ctx)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (separated : cells.TransportSeparated transport) :
    (cells.underWorkspace key shape fresh).TransportSeparated
      (transport.underWorkspace key shape fresh) := by
  induction cells with
  | nil => trivial
  | cons head tail ih =>
      refine ⟨?_, ih separated.2⟩
      intro observed input
      rw [Transport.liftInput_underWorkspace]
      change head.ref.key ∉
        ((transport.liftInput input).underWorkspace key shape fresh).storageKeys
      rw [CInputRef.storageKeys_underWorkspace]
      exact separated.1 input

theorem workspaceCells_transportSeparated_extend {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (transport : Transport outer ctx)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (separated : cells.TransportSeparated transport) :
    TransportSeparated
      (.cons { ref := CWriteRef.workspaceHead ctx key shape fresh, role := rfl }
        (cells.underWorkspace key shape fresh))
      (transport.underWorkspace key shape fresh) := by
  refine ⟨?_, workspaceCells_transportSeparated_underWorkspace
    cells transport key shape fresh separated⟩
  intro observed input
  rw [Transport.liftInput_underWorkspace]
  change key ∉ ((transport.liftInput input).underWorkspace key shape fresh).storageKeys
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun member => fresh (CInputRef.storageKeys_subset_context _ member)

public theorem workspaceCells_transportSeparated_avoids_of_mem {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport)
    {key : StorageKey} (member : key ∈ cells.keys)
    {shape : CShape} (input : CInputRef outer shape) :
    key ∉ (transport.liftInput input).storageKeys := by
  induction cells with
  | nil => simp [keys] at member
  | cons head tail ih =>
      simp only [keys, List.mem_cons] at member
      rcases member with rfl | member
      · exact separated.1 input
      · exact ih separated.2 member

/-- An indexed workspace cell is disjoint from all transported caller reads. -/
public theorem workspaceCells_cellAt_transport_avoids {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport)
    {shape : CShape} (input : CInputRef outer shape) (index : Fin shapes.length) :
    (cellAt cells index).ref.key ∉ (transport.liftInput input).storageKeys :=
  workspaceCells_transportSeparated_avoids_of_mem cells transport separated
    (workspaceCells_cellAt_key_mem_keys cells index) input

end QuantumAlg.Execution.ClassicalWorkspace.Cells
