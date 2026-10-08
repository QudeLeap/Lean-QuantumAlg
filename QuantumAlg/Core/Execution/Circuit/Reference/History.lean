/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.Reference
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Complete history coordinates under reference transport

Transporting the external reference and mapping the mathematical history
commute with the actual circuit execution. The explicit history map acts on
the actual hidden service value and path, summing complete quantum blocks
when several records share an output. The physical final store is unchanged.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

/-- Finite history maps commute with actual execution and external-reference transport. -/
theorem execute_mapHistory_reference {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} (code : Circuit model pre post)
    (Reference Other : Register) {H K L : Type}
    [Fintype H] [Fintype K] [Fintype L]
    (state : State pre Reference (model.HiddenState × H))
    (initial : H → K) (final : model.HiddenState × (K × code.Path) → L)
    (basis : Reference.Index ≃ Other.Index) :
    State.mapHistory (ctx := post)
      ((code.execute Reference
        (State.mapHistory (ctx := pre) state
          (fun record => (record.1, initial record.2)))).reindex
        (S := Register.prod post.register Other)
        ((Equiv.refl post.register.Index).prodCongr basis)) final =
      (State.mapHistory (ctx := post) (code.execute Reference state)
        (fun record => final (record.1, (initial record.2.1, record.2.2)))).reindex
        (S := Register.prod post.register Other)
        ((Equiv.refl post.register.Index).prodCongr basis) := by
  have mapped := congrArg
    (fun result : State post Reference (model.HiddenState × (K × code.Path)) =>
      State.mapHistory (ctx := post)
        (result.reindex (S := Register.prod post.register Other)
          ((Equiv.refl post.register.Index).prodCongr basis)) final)
    (execute_mapHistory code Reference state initial)
  refine mapped.trans ?_
  rw [State.reference_history, State.mapHistory_comp]
  rfl

end

end QuantumAlg.Circuit
