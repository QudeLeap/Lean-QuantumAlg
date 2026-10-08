/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store
/-!
# Initialized allocation contracts on restricted actual stores
The body's caller-store relation uses restriction of the same actual stores
that occur in the complete interpreter equation. Allocation supplies the
initialization premise, and lexical release returns that actual caller store.
-/
namespace QuantumAlg.Execution.ClassicalWorkspace
noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α
/-- Restriction expresses the initialized body contract on actual caller stores. -/
theorem withCells_actualRecord_initialized_restricted_post {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (transport : Transport ctx inner) → cells.TransportSeparated transport →
        Circuit model inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (transport : Transport ctx inner)
      (separated : cells.TransportSeparated transport),
      ∃ step : Store inner × model.HiddenState →
        (Store inner × model.HiddenState) × (body cells distinct transport separated).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference (model.HiddenState × History)),
          (body cells distinct transport separated).execute Reference state =
            state.mapClassical (fun entry =>
              let result := step (entry.1, entry.2.1)
              (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
        ∀ before : Store inner × model.HiddenState, cells.Initialized before.1 →
          Post (transport.restrict before.1) (transport.restrict (step before).1.1)) :
    ∃ step : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (withCells ctx shapes body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withCells ctx shapes body).execute Reference state =
          state.mapClassical (fun entry =>
            let result := step (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, Post before.1 (step before).1.1 := by
  apply withCells_actualRecord_initialized_post ctx shapes body Post
  intro inner cells distinct transport separated
  obtain ⟨step, equation, correct⟩ := bodyContract cells distinct transport separated
  refine ⟨step, equation, ?_⟩
  intro source before reads initialized
  refine ⟨transport.restrict (step before).1.1, ?_,
    transport.workspaceTransport_restrict_readsAs _⟩
  simpa only [(transport.workspaceTransport_readsAs_restrict_iff).mp reads] using
    correct before initialized

/-- A store-only body retains its store-only record through initialized allocation and release. -/
theorem withCells_actualStoreRecord_initialized_restricted_post {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (transport : Transport ctx inner) → cells.TransportSeparated transport →
        Circuit model inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (transport : Transport ctx inner)
      (separated : cells.TransportSeparated transport),
      ∃ step : Store inner → Store inner × (body cells distinct transport separated).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference (model.HiddenState × History)),
          (body cells distinct transport separated).execute Reference state =
            state.mapClassical (fun entry =>
              let result := step entry.1
              (result.1, (entry.2.1, (entry.2.2, result.2))))) ∧
        ∀ before : Store inner, cells.Initialized before →
          Post (transport.restrict before) (transport.restrict (step before).1)) :
    ∃ step : Store ctx → Store ctx × (withCells ctx shapes body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withCells ctx shapes body).execute Reference state =
          state.mapClassical (fun entry =>
            let result := step entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  apply withCells_actualStoreRecord_initialized_post ctx shapes body Post
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
