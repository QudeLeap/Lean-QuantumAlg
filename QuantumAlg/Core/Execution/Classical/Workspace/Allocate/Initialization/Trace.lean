/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Trace

/-!
# Exact actual traces through initialized heterogeneous allocation

The same actual record certifies the complete interpreter and a relation
between the incoming caller store and its event list. Real lexical entry
supplies every internal initialization premise; push and pop add no events.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Initialized actual body traces remain the traces of their actual enclosing lexical record. -/
theorem withCellsFrom_actualRecord_initialized_trace {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit inner inner)
    (Trace : Store outer → List (Resource.Event kind) → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport),
      ∃ step : Store inner → Store inner × (body cells distinct innerTransport separated).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body cells distinct innerTransport separated).execute Reference state =
            state.mapClassical (fun entry =>
              ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
        ∀ (source : Store outer) (before : Store inner),
          innerTransport.ReadsAs source before → cells.Initialized before →
            Trace source ((body cells distinct innerTransport separated).eventTrace
              (step before).2)) :
    ∃ step : Store ctx → Store ctx × (withCellsFrom transport shapes body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withCellsFrom transport shapes body).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ (source : Store outer) (before : Store ctx), transport.ReadsAs source before →
        Trace source ((withCellsFrom transport shapes body).eventTrace (step before).2) := by
  induction shapes with
  | nil =>
      obtain ⟨step, equation, correct⟩ := bodyContract .nil (by trivial) transport (by trivial)
      refine ⟨step, equation, ?_⟩
      intro source before reads
      exact correct source before reads (by trivial)
  | cons shape shapes inductionHypothesis =>
      dsimp only [withCellsFrom]
      apply inductionHypothesis
      intro inner cells distinct innerTransport separated
      let key := inner.canonicalFreshKey
      let fresh : key ∉ inner.keys := inner.canonicalFreshKey_fresh
      let head : Cell (inner.addWorkspace key shape fresh) shape :=
        { ref := CWriteRef.workspaceHead inner key shape fresh, role := rfl }
      let allCells := Cells.cons head (cells.underWorkspace key shape fresh)
      have allDistinct : allCells.Distinct :=
        Cells.workspaceCells_cons_distinct head (cells.underWorkspace key shape fresh)
          (Cells.workspaceCells_underWorkspace_avoids_fresh cells key shape fresh)
          (Cells.workspaceCells_underWorkspace_distinct cells distinct key shape fresh)
      have allSeparated : allCells.TransportSeparated
          (innerTransport.underWorkspace key shape fresh) :=
        Cells.workspaceCells_transportSeparated_extend cells innerTransport
          key shape fresh separated
      obtain ⟨step, equation, correct⟩ := bodyContract allCells allDistinct
        (innerTransport.underWorkspace key shape fresh) allSeparated
      refine ⟨Circuit.workspaceRecord key shape fresh _ step,
        Circuit.execute_workspaceRecord key shape fresh _ step equation, ?_⟩
      intro source before reads initialized
      exact correct source (before.pushWorkspace key shape fresh)
        (innerTransport.workspaceTransport_readsAs_pushWorkspace key shape fresh reads)
        (Cells.workspaceCells_initialized_extend cells before key shape fresh initialized)

/-- Direct actual allocation establishes the internal premises of a caller-indexed trace law. -/
theorem withCells_actualRecord_initialized_trace {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes), cells.Distinct →
      (transport : Transport ctx inner) → cells.TransportSeparated transport →
        Circuit inner inner)
    (Trace : Store ctx → List (Resource.Event kind) → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (transport : Transport ctx inner)
      (separated : cells.TransportSeparated transport),
      ∃ step : Store inner → Store inner × (body cells distinct transport separated).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body cells distinct transport separated).execute Reference state =
            state.mapClassical (fun entry =>
              ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
        ∀ (source : Store ctx) (before : Store inner), transport.ReadsAs source before →
          cells.Initialized before →
            Trace source ((body cells distinct transport separated).eventTrace (step before).2)) :
    ∃ step : Store ctx → Store ctx × (withCells ctx shapes body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withCells ctx shapes body).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ before : Store ctx,
        Trace before ((withCells ctx shapes body).eventTrace (step before).2) := by
  obtain ⟨step, equation, correct⟩ :=
    withCellsFrom_actualRecord_initialized_trace (Transport.id ctx) shapes body Trace bodyContract
  exact ⟨step, equation, fun before => correct before before
    (Transport.workspaceTransport_readsAs_id before)⟩

end

end QuantumAlg.Execution.ClassicalWorkspace
