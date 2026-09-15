/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Record

/-!
# Actual initialized-cell contracts through heterogeneous lexical allocation

The allocation instructions establish the initial values required by the body.
The complete interpreter equation and returned caller-store postcondition use
the same actual record, without imposing initialization on the caller store.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Fresh allocation establishes the initialized-cell premise of the actual body contract. -/
theorem withCellsFrom_actualRecord_initialized_post {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit inner inner)
    (Post : Store outer → Store outer → Prop)
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
            ∃ target : Store outer, Post source target ∧
              innerTransport.ReadsAs target (step before).1) :
    ∃ step : Store ctx → Store ctx × (withCellsFrom transport shapes body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withCellsFrom transport shapes body).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ (source : Store outer) (before : Store ctx), transport.ReadsAs source before →
        ∃ target : Store outer, Post source target ∧ transport.ReadsAs target (step before).1 := by
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
      obtain ⟨target, post, returned⟩ := correct source (before.pushWorkspace key shape fresh)
        (innerTransport.workspaceTransport_readsAs_pushWorkspace key shape fresh reads)
        (Cells.workspaceCells_initialized_extend cells before key shape fresh initialized)
      exact ⟨target, post,
        innerTransport.workspaceTransport_readsAs_popWorkspace key shape fresh returned⟩

/-- Direct allocation supplies initialized cells and returns the actual caller postcondition. -/
theorem withCells_actualRecord_initialized_post {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes), cells.Distinct →
      (transport : Transport ctx inner) → cells.TransportSeparated transport →
        Circuit inner inner)
    (Post : Store ctx → Store ctx → Prop)
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
            ∃ target : Store ctx, Post source target ∧ transport.ReadsAs target (step before).1) :
    ∃ step : Store ctx → Store ctx × (withCells ctx shapes body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withCells ctx shapes body).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  obtain ⟨step, equation, correct⟩ :=
    withCellsFrom_actualRecord_initialized_post (Transport.id ctx) shapes body Post bodyContract
  refine ⟨step, equation, ?_⟩
  intro before
  obtain ⟨target, post, returned⟩ := correct before before
    (Transport.workspaceTransport_readsAs_id before)
  have same : (step before).1 = target :=
    Transport.workspaceTransport_readsAs_id_iff.mp returned
  simpa only [same] using post

end

end QuantumAlg.Execution.ClassicalWorkspace
