/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store

/-!
# One initialized allocation record for every execution environment

A fixed store-only body record lifts through lexical allocation and release before
an execution environment is supplied. The same record retains every incoming
history and quantum-reference block and satisfies the caller-store postcondition.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Fresh allocation supplies initialized cells to a deterministic store-only body while
preserving the selected execution model's service state. -/
lemma withCellsFrom_actualStoreRecord_initialized_uniform_post {model : ExecutionModel}
    {outer ctx : RuntimeCtx model.kind} (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit model inner inner)
    (Post : Store outer → Store outer → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport),
      ∃ step : Store inner → Store inner × (body cells distinct innerTransport separated).Path,
        (∀ (environment : model.Environment) (Reference : Register) {History : Type} [Fintype
          History]
          (state : State inner Reference (model.HiddenState × History)),
          (body cells distinct innerTransport separated).execute environment Reference state =
            state.mapClassical (fun entry =>
              let result := step entry.1
              (result.1, (entry.2.1, (entry.2.2, result.2))))) ∧
        ∀ (source : Store outer) (before : Store inner),
          innerTransport.ReadsAs source before → cells.Initialized before →
            ∃ target : Store outer, Post source target ∧
              innerTransport.ReadsAs target (step before).1) :
    ∃ step : Store ctx → Store ctx × (withCellsFrom transport shapes body).Path,
      (∀ (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withCellsFrom transport shapes body).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := step entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2))))) ∧
      ∀ (source : Store outer) (before : Store ctx), transport.ReadsAs source before →
        ∃ target : Store outer, Post source target ∧
          transport.ReadsAs target (step before).1 := by
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
      refine ⟨Circuit.workspaceStoreRecord key shape fresh _ step,
        (fun environment => Circuit.execute_workspaceStoreRecord environment
          key shape fresh _ step (equation environment)), ?_⟩
      intro source before reads initialized
      obtain ⟨target, post, returned⟩ :=
        correct source (before.pushWorkspace key shape fresh)
          (innerTransport.workspaceTransport_readsAs_pushWorkspace key shape fresh reads)
          (Cells.workspaceCells_initialized_extend cells before key shape fresh initialized)
      exact ⟨target, post,
        innerTransport.workspaceTransport_readsAs_popWorkspace key shape fresh returned⟩

/-- Direct allocation supplies initialized cells to a deterministic store-only body. -/
lemma withCells_actualStoreRecord_initialized_uniform_post {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (transport : Transport ctx inner) → cells.TransportSeparated transport →
        Circuit model inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (transport : Transport ctx inner)
      (separated : cells.TransportSeparated transport),
      ∃ step : Store inner → Store inner × (body cells distinct transport separated).Path,
        (∀ (environment : model.Environment) (Reference : Register) {History : Type} [Fintype
          History]
          (state : State inner Reference (model.HiddenState × History)),
          (body cells distinct transport separated).execute environment Reference state =
            state.mapClassical (fun entry =>
              let result := step entry.1
              (result.1, (entry.2.1, (entry.2.2, result.2))))) ∧
        ∀ (source : Store ctx) (before : Store inner), transport.ReadsAs source before →
          cells.Initialized before →
            ∃ target : Store ctx, Post source target ∧ transport.ReadsAs target (step before).1) :
    ∃ step : Store ctx → Store ctx × (withCells ctx shapes body).Path,
      (∀ (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withCells ctx shapes body).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := step entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  obtain ⟨step, equation, correct⟩ :=
    withCellsFrom_actualStoreRecord_initialized_uniform_post (Transport.id ctx) shapes body Post
      bodyContract
  refine ⟨step, equation, ?_⟩
  intro before
  obtain ⟨target, post, returned⟩ := correct before before
    (Transport.workspaceTransport_readsAs_id before)
  have same : (step before).1 = target :=
    Transport.workspaceTransport_readsAs_id_iff.mp returned
  simpa only [same] using post


/-- A store-only body retains its store-only record through initialized allocation and release. -/
lemma withCells_actualStoreRecord_initialized_uniform_restricted_post {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (transport : Transport ctx inner) → cells.TransportSeparated transport →
        Circuit model inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (transport : Transport ctx inner)
      (separated : cells.TransportSeparated transport),
      ∃ step : Store inner → Store inner × (body cells distinct transport separated).Path,
        (∀ (environment : model.Environment) (Reference : Register) {History : Type} [Fintype
          History]
          (state : State inner Reference (model.HiddenState × History)),
          (body cells distinct transport separated).execute environment Reference state =
            state.mapClassical (fun entry =>
              let result := step entry.1
              (result.1, (entry.2.1, (entry.2.2, result.2))))) ∧
        ∀ before : Store inner, cells.Initialized before →
          Post (transport.restrict before) (transport.restrict (step before).1)) :
    ∃ step : Store ctx → Store ctx × (withCells ctx shapes body).Path,
      (∀ (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withCells ctx shapes body).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := step entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  apply withCells_actualStoreRecord_initialized_uniform_post ctx shapes body Post
  intro inner cells distinct transport separated
  obtain ⟨step, equation, correct⟩ := bodyContract cells distinct transport separated
  refine ⟨step, equation, ?_⟩
  intro source before reads initialized
  refine ⟨transport.restrict (step before).1, ?_,
    transport.workspaceTransport_restrict_readsAs _⟩
  simpa only [(transport.workspaceTransport_readsAs_restrict_iff).mp reads] using
    correct before initialized

end

end QuantumAlg.Execution.ClassicalWorkspace
