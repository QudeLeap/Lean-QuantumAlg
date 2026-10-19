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
lemma withCellsFrom_hasRecord {model : ExecutionModel}
    (environment : model.Environment) {outer ctx : RuntimeCtx model.kind}
    (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
        Circuit model inner inner)
    (bodyRecord : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport),
      ∃ step : Store inner × model.HiddenState →
        (Store inner × model.HiddenState) × (body cells distinct innerTransport separated).Path,
        ∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference (model.HiddenState × History)),
          (body cells distinct innerTransport separated).execute environment Reference state =
            state.mapClassical (fun entry =>
              let result := step (entry.1, entry.2.1)
              (result.1.1, (result.1.2, (entry.2.2, result.2))))) :
    ∃ step : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (withCellsFrom transport shapes body).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withCellsFrom transport shapes body).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := step (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply withCellsFrom_property transport shapes body
    (fun {inner} _ code => ∃ step : Store inner × model.HiddenState →
      (Store inner × model.HiddenState) × code.Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State inner Reference (model.HiddenState × History)),
        code.execute environment Reference state = state.mapClassical (fun entry =>
          let result := step (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2)))))
  · intro inner innerTransport key shape fresh code available
    obtain ⟨step, equation⟩ := available
    exact ⟨Circuit.workspaceRecord key shape fresh code step,
      Circuit.execute_workspaceRecord environment key shape fresh code step equation⟩
  · exact bodyRecord
end
end QuantumAlg.Execution.ClassicalWorkspace
