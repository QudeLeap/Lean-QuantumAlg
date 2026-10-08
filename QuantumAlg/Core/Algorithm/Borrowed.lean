/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Borrowed restoration at the complete run boundary

Recording the original store as mathematical history leaves its complete
borrowed observation unchanged. A circuit restoration law therefore supplies
the corresponding run law while preserving the actual hidden service state.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A circuit law for every incoming history also restores the complete caller observation. -/
theorem restoresBorrowed_of_circuit {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (run : AlgorithmRun model pre post shape)
    (restores : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State pre Reference (model.HiddenState × History)),
      run.code.BorrowedRestored Reference state (run.code.execute Reference state))
    {Reference : Register} (input : OracleInput model.classicalOracles pre Reference) :
    run.RestoresBorrowed input := by
  have actual := restores Reference
    (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
  refine actual.trans ?_
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block]
  congr 1
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  rfl

end

end QuantumAlg.AlgorithmRun
