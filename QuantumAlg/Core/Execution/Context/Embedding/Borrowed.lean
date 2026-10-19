/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding.Selection
public import QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Context.Embedding.Selection
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Base.Accounting.Context.Relabeling
import Mathlib.Logic.Equiv.Sum

/-!
# Borrowed wires under actual physical placement

Borrowed membership follows the original entry role through relabeling,
disjoint union and entry permutation. The caller's borrowed positions are
exactly the disjoint union of the original local and complement borrowed
positions. These statements identify physical wires, including their native
dimensions, before transporting any state [dW19, qcnotes.tex:389,5381].
-/

namespace QuantumAlg

namespace RuntimeEntry

/-- Physical placement preserves the borrowed role and maps every borrowed wire. -/
lemma runtimeEntry_relabel_borrowedQuantumWires {kind : ProblemKind}
    (entry : RuntimeEntry kind) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    (entry.relabel keys physical).borrowedQuantumWires =
      entry.borrowedQuantumWires.map (QuantumWire.relabel physical) := by
  cases entry with
  | storage => rfl
  | borrowedLayout => exact QuantumLayout.relabel_wires _ _
  | suppliedLayout | ownedLayout | ownedCopies => rfl

/-- A placed borrowed classical cell retains its original role and value shape. -/
lemma runtimeEntry_relabel_borrowedClassicalCells {kind : ProblemKind}
    (entry : RuntimeEntry kind) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    (entry.relabel keys physical).borrowedClassicalCells =
      entry.borrowedClassicalCells.map (fun cell => (keys cell.1, cell.2)) := by
  cases entry with
  | storage key role shape => cases role <;> rfl
  | borrowedLayout | suppliedLayout | ownedLayout | ownedCopies => rfl

end RuntimeEntry

namespace RuntimeCtx

/-- Relabeling preserves the complete ordered borrowed wire list. -/
lemma runtimeCtx_relabel_borrowedQuantumWires {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    (ctx.relabel keys physical).borrowedQuantumWires =
      ctx.borrowedQuantumWires.map (QuantumWire.relabel physical) := by
  change (ctx.entries.map (RuntimeEntry.relabel keys physical)).flatMap
    RuntimeEntry.borrowedQuantumWires = _
  simp only [borrowedQuantumWires, List.flatMap_map, List.map_flatMap,
    RuntimeEntry.runtimeEntry_relabel_borrowedQuantumWires]

/-- Relabeling retains each borrowed classical cell without changing its shape. -/
lemma runtimeCtx_relabel_borrowedClassicalCells {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    (ctx.relabel keys physical).borrowedClassicalCells =
      ctx.borrowedClassicalCells.map (fun cell => (keys cell.1, cell.2)) := by
  change (ctx.entries.map (RuntimeEntry.relabel keys physical)).flatMap
    RuntimeEntry.borrowedClassicalCells = _
  simp only [borrowedClassicalCells, List.flatMap_map, List.map_flatMap,
    RuntimeEntry.runtimeEntry_relabel_borrowedClassicalCells]

end RuntimeCtx

namespace ContextEmbedding

noncomputable section

open Execution

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- The caller contains precisely the original borrowed wire records from both sides. -/
lemma contextEmbedding_borrowedQuantumWires_perm :
    (localCtx.borrowedQuantumWires.map (QuantumWire.relabel placement.physical) ++
      placement.frame.borrowedQuantumWires).Perm caller.borrowedQuantumWires := by
  have permuted := List.Perm.flatMap_right RuntimeEntry.borrowedQuantumWires placement.covers
  change (((localCtx.relabel placement.keys placement.physical).entries ++
    placement.frame.entries).flatMap RuntimeEntry.borrowedQuantumWires).Perm
      caller.borrowedQuantumWires at permuted
  rw [List.flatMap_append] at permuted
  change ((localCtx.relabel placement.keys placement.physical).borrowedQuantumWires ++
    placement.frame.borrowedQuantumWires).Perm caller.borrowedQuantumWires at permuted
  rw [RuntimeCtx.runtimeCtx_relabel_borrowedQuantumWires] at permuted
  exact permuted

/-- The caller's borrowed classical cells retain all original keys, roles and shapes. -/
lemma contextEmbedding_borrowedClassicalCells_perm :
    (localCtx.borrowedClassicalCells.map (fun cell => (placement.keys cell.1, cell.2)) ++
      placement.frame.borrowedClassicalCells).Perm caller.borrowedClassicalCells := by
  have permuted := List.Perm.flatMap_right RuntimeEntry.borrowedClassicalCells placement.covers
  change (((localCtx.relabel placement.keys placement.physical).entries ++
    placement.frame.entries).flatMap RuntimeEntry.borrowedClassicalCells).Perm
      caller.borrowedClassicalCells at permuted
  rw [List.flatMap_append] at permuted
  change ((localCtx.relabel placement.keys placement.physical).borrowedClassicalCells ++
    placement.frame.borrowedClassicalCells).Perm caller.borrowedClassicalCells at permuted
  rw [RuntimeCtx.runtimeCtx_relabel_borrowedClassicalCells] at permuted
  exact permuted

private lemma local_wire_not_frame (index : Fin localCtx.systemCount) :
    QuantumWire.relabel placement.physical (localCtx.quantumLayout.wire index) ∉
      placement.frame.borrowedQuantumWires := by
  intro member
  have localLive : localCtx.quantumLayout.wire index ∈ localCtx.quantumWires := by
    rw [← RuntimeCtx.quantumLayout_wires]
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  have placedLive : QuantumWire.relabel placement.physical (localCtx.quantumLayout.wire index) ∈
      (localCtx.relabel placement.keys placement.physical).quantumWires := by
    rw [RuntimeCtx.relabel_quantumWires]
    exact List.mem_map_of_mem localLive
  exact ((RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp placement.separate.2)
    (List.mem_map_of_mem placedLive)
    (List.mem_map_of_mem (placement.frame.borrowedQuantumWires_sublist.subset member))

private lemma frame_wire_not_local (index : Fin placement.frame.systemCount) :
    placement.frame.quantumLayout.wire index ∉
      localCtx.borrowedQuantumWires.map (QuantumWire.relabel placement.physical) := by
  intro member
  have placedLive : placement.frame.quantumLayout.wire index ∈
      (localCtx.relabel placement.keys placement.physical).quantumWires := by
    rw [RuntimeCtx.relabel_quantumWires]
    exact (localCtx.borrowedQuantumWires_sublist.map
      (QuantumWire.relabel placement.physical)).subset member
  have frameLive : placement.frame.quantumLayout.wire index ∈
      placement.frame.quantumWires := by
    rw [← RuntimeCtx.quantumLayout_wires]
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  exact ((RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp placement.separate.2)
    (List.mem_map_of_mem placedLive) (List.mem_map_of_mem frameLive)

/-- A placed local wire is borrowed exactly when its original entry was borrowed. -/
lemma contextEmbedding_local_borrowed_iff (index : Fin localCtx.systemCount) :
    placement.position index ∈ caller.borrowedSelection ↔ index ∈ localCtx.borrowedSelection := by
  rw [RuntimeCtx.mem_borrowedSelection, placement.contextEmbedding_position_wire,
    ← placement.contextEmbedding_borrowedQuantumWires_perm.mem_iff, List.mem_append,
    List.mem_map_of_injective (QuantumWire.relabel_injective placement.physical)]
  simp only [placement.local_wire_not_frame index, or_false, RuntimeCtx.mem_borrowedSelection]

/-- Complement wires retain exactly their original borrowed status. -/
lemma contextEmbedding_frame_borrowed_iff (index : Fin placement.frame.systemCount) :
    placement.positions (.inr index) ∈ caller.borrowedSelection ↔
      index ∈ placement.frame.borrowedSelection := by
  rw [RuntimeCtx.mem_borrowedSelection, placement.contextEmbedding_frame_position_wire,
    ← placement.contextEmbedding_borrowedQuantumWires_perm.mem_iff, List.mem_append]
  simp only [placement.frame_wire_not_local index, false_or, RuntimeCtx.mem_borrowedSelection]

/-- Every borrowed caller position has precisely one original borrowed-side position. -/
def borrowedPositions :
    QuantumLayout.SelectedPosition localCtx.borrowedSelection ⊕
      QuantumLayout.SelectedPosition placement.frame.borrowedSelection ≃
        QuantumLayout.SelectedPosition caller.borrowedSelection :=
  (Equiv.subtypeSum (p := fun index =>
    match index with
    | .inl localIndex => localIndex ∈ localCtx.borrowedSelection
    | .inr frameIndex => frameIndex ∈ placement.frame.borrowedSelection)).symm.trans
      (placement.positions.subtypeEquiv fun index => by
        cases index with
        | inl index => exact (placement.contextEmbedding_local_borrowed_iff index).symm
        | inr index => exact (placement.contextEmbedding_frame_borrowed_iff index).symm)

/-- The borrowed-side correspondence uses the actual placed local position. -/
lemma contextEmbedding_borrowedPositions_local
    (index : QuantumLayout.SelectedPosition localCtx.borrowedSelection) :
    (placement.borrowedPositions (.inl index)).val = placement.position index.val := rfl

/-- The borrowed-side correspondence uses the actual unchanged complement position. -/
lemma contextEmbedding_borrowedPositions_frame
    (index : QuantumLayout.SelectedPosition placement.frame.borrowedSelection) :
    (placement.borrowedPositions (.inr index)).val = placement.positions (.inr index.val) := rfl

end

end ContextEmbedding

end QuantumAlg
