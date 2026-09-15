/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Induction
import all QuantumAlg.Core.Execution.Classical.Workspace.Record
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Read

/-!
# Actual-store postconditions through heterogeneous lexical allocation

The same record witnesses the full interpreter equation and the relation
between incoming and returned caller stores. Each lexical step uses the real
workspace record, retaining its actual path and all quantum-reference blocks.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Lift an actual body record and caller-store postcondition through lexical allocation. -/
theorem withCellsFrom_actualRecord_post {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    (transport : Transport outer ctx) (shapes : List CShape)
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
          innerTransport.ReadsAs source before →
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
  apply withCellsFrom_property transport shapes body
    (fun {inner} currentTransport code => ∃ step : Store inner → Store inner × code.Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State inner Reference History),
        code.execute Reference state = state.mapClassical (fun entry =>
          ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ (source : Store outer) (before : Store inner), currentTransport.ReadsAs source before →
        ∃ target : Store outer, Post source target ∧
          currentTransport.ReadsAs target (step before).1)
  · intro inner innerTransport key shape fresh code available
    obtain ⟨step, equation, correct⟩ := available
    refine ⟨Circuit.workspaceRecord key shape fresh code step,
      Circuit.execute_workspaceRecord key shape fresh code step equation, ?_⟩
    intro source before reads
    obtain ⟨target, post, returned⟩ := correct source (before.pushWorkspace key shape fresh)
      (innerTransport.workspaceTransport_readsAs_pushWorkspace key shape fresh reads)
    exact ⟨target, post,
      innerTransport.workspaceTransport_readsAs_popWorkspace key shape fresh returned⟩
  · exact bodyContract

/-- Direct allocation returns the actual caller store satisfying the two-store postcondition. -/
theorem withCells_actualRecord_post {kind : ProblemKind} (ctx : RuntimeCtx kind)
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
          ∃ target : Store ctx, Post source target ∧ transport.ReadsAs target (step before).1) :
    ∃ step : Store ctx → Store ctx × (withCells ctx shapes body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withCells ctx shapes body).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  obtain ⟨step, equation, correct⟩ :=
    withCellsFrom_actualRecord_post (Transport.id ctx) shapes body Post bodyContract
  refine ⟨step, equation, ?_⟩
  intro before
  obtain ⟨target, post, returned⟩ := correct before before
    (Transport.workspaceTransport_readsAs_id before)
  have same : (step before).1 = target :=
    Transport.workspaceTransport_readsAs_id_iff.mp returned
  simpa only [same] using post

end

end QuantumAlg.Execution.ClassicalWorkspace
