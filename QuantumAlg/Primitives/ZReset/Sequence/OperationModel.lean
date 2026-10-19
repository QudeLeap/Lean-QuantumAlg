/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Sequence
import all QuantumAlg.Primitives.ZReset.Circuit.OperationModel
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.State.History

/-!
# Classical-language independence of a physical reset sequence

An additional classical operation grant does not alter the result of the
actual measurement-and-correction sequence. Only its mathematical path type
can vary with the selected model; the complete final store, persistent service
state and quantum-reference blocks agree after erasing that path.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

variable {services : ClassicalOracleModel}

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
  {environment : (ExecutionModel.quantum gates oracles .empty services).Environment}
  (implementations : ∀ wire,
    QuditShift.Realizations gates oracles ctx.quantumLayout wire)

/-- Changing only the classical operation grant preserves the complete output
state after dropping the reset path record. -/
lemma sequence_execute_operationModel {allowAllocation : Bool} (readouts : List (ZReadout ctx))
    (operations : ClassicalOpModel) {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum gates oracles .empty services).HiddenState × History)) :
    ((sequence (allowAllocation := allowAllocation) (services := services) implementations readouts
        operations).execute
      ⟨environment.quantum, environment.classical⟩ Reference
      state).mapHistory
      (fun record => (record.1, record.2.1)) =
    ((sequence (allowAllocation := allowAllocation) (services := services) implementations
        readouts).execute
      ⟨environment.quantum, environment.classical⟩ Reference state).mapHistory
      (fun record => (record.1, record.2.1)) := by
  induction readouts generalizing History with
  | nil => rfl
  | cons head tail ih =>
      simp only [sequence, Circuit.execute_seq]
      rw [circuit_execute_operationModel (allowAllocation := allowAllocation) head.wire head.output
        (implementations head.wire) operations state]
      have tailEq := ih
        ((circuit (allowAllocation := allowAllocation) (services := services) head.wire head.output
            (implementations head.wire)).execute
      ⟨environment.quantum, environment.classical⟩ Reference state)
      have erased := congrArg
        (fun output : State ctx Reference
          ((ExecutionModel.quantum gates oracles .empty services).HiddenState ×
            (History × (circuit (allowAllocation := allowAllocation) (services := services)
                head.wire head.output
              (implementations head.wire)).Path)) =>
          output.mapHistory (fun record => (record.1, record.2.1))) tailEq
      erw [State.mapHistory_comp, State.mapHistory_comp]
      erw [State.mapHistory_comp, State.mapHistory_comp] at erased
      exact erased

end

end QuantumAlg.ZReset
