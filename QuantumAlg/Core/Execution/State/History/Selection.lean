/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Quantum.HistorySelection
import all QuantumAlg.Core.Execution.Classical.MapLaws
import all QuantumAlg.Core.Execution.State

/-!
# Complete unchanged-history fibers of actual instructions

An earlier history label may carry an entire classical spectator store.
Selecting its fiber keeps the full quantum/reference density block. Actual
unitary and Z instructions commute with this mathematical selection; the
measurement still writes its real outcome to its designated classical cell
[dW19, qcnotes.tex:5381,5409]. No physical operation or space release is added.
-/

namespace QuantumAlg.Execution.State

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H K D : Type} [Fintype H] [Fintype K] [DecidableEq D]

/-- Select an earlier history value while retaining every physical store and quantum block. -/
def selectHistory (state : State ctx Reference H) (read : H → D) (value : D) :
    State ctx Reference H :=
  state.selectClassical (fun record => read record.2) value

/-- A history map selects precisely the original histories in the requested output fiber. -/
theorem selectHistory_mapHistory (state : State ctx Reference H) (update : H → K)
    (read : K → D) (value : D) :
    (state.mapHistory update).selectHistory read value =
      (state.selectHistory (read ∘ update) value).mapHistory update :=
  ExecutionState.mapClassical_selectClassical state
    (fun record => (record.1, update record.2)) (fun record => read record.2) value

/-- The unique deterministic path preserves each complete earlier-history fiber. -/
theorem selectHistory_skip (state : State ctx Reference H) (read : H → D) (value : D) :
    state.skip.selectHistory (fun record => read record.1) value =
      (state.selectHistory read value).skip :=
  selectHistory_mapHistory state (fun history => (history, ()))
    (fun record => read record.1) value

section Quantum

variable {ctx : RuntimeCtx .quantum}

/-- Actual unitary execution retains the original-history selection exactly. -/
theorem selectHistory_unitary (state : State ctx Reference H)
    (program : UnitaryOperator ctx.register) (read : H → D) (value : D) :
    (state.unitary program).selectHistory (fun record => read record.1) value =
      (state.selectHistory read value).unitary program := by
  dsimp only [unitary, selectHistory]
  rw [ExecutionState.mapClassical_selectClassical,
    ExecutionState.selectClassical_applyUnitary]
  rfl

/-- Actual Z measurement and its real store write preserve every earlier-history fiber. -/
theorem selectHistory_measureZ (state : State ctx Reference H)
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (read : H → D) (value : D) :
    (state.measureZ wire output).selectHistory (fun record => read record.1) value =
      (state.selectHistory read value).measureZ wire output := by
  dsimp only [measureZ, selectHistory]
  rw [ExecutionState.mapClassical_selectClassical]
  dsimp only [Function.comp_def]
  rw [ExecutionState.selectClassical_measureZ state (fun basis => basis.1 wire)
    (fun record => read record.2) value]

end Quantum

end

end QuantumAlg.Execution.State
