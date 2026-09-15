/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Induction
import all QuantumAlg.Core.Execution.Classical.Workspace.Record

/-!
# Exact classical records through heterogeneous workspace allocation

The conclusion is an equation for the existing Circuit interpreter on the full
quantum-reference state. Each witness is composed from the body's proved record
by actual Store push and pop operations; it is not an alternative semantics.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A deterministic actual body has a deterministic full-state record after lexical allocation. -/
theorem withCellsFrom_hasRecord {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit inner inner)
    (bodyRecord : ∀ {inner : RuntimeCtx kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport),
      ∃ step : Store inner → Store inner × (body cells distinct innerTransport separated).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body cells distinct innerTransport separated).execute Reference state =
            state.mapClassical (fun entry =>
              ((step entry.1).1, (entry.2, (step entry.1).2)))) :
    ∃ step : Store ctx → Store ctx × (withCellsFrom transport shapes body).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withCellsFrom transport shapes body).execute Reference state =
          state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2))) := by
  apply withCellsFrom_property transport shapes body
    (fun {inner} _ code => ∃ step : Store inner → Store inner × code.Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State inner Reference History),
        code.execute Reference state = state.mapClassical (fun entry =>
          ((step entry.1).1, (entry.2, (step entry.1).2))))
  · intro inner innerTransport key shape fresh code available
    obtain ⟨step, equation⟩ := available
    exact ⟨Circuit.workspaceRecord key shape fresh code step,
      Circuit.execute_workspaceRecord key shape fresh code step equation⟩
  · exact bodyRecord

end

end QuantumAlg.Execution.ClassicalWorkspace
