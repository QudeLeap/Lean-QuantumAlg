/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Support

/-! # Supported Stores through actual circuit sequencing -/

namespace QuantumAlg.Circuit

open Execution
noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Rebracketing the complete sequential history preserves every Store
property established by the actual second execution. -/
lemma supported_store_seq {model : ExecutionModel}
    {initial middle final : RuntimeCtx model.kind}
    (environment : model.Environment)
    (first : Circuit model initial middle) (second : Circuit model middle final)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State initial Reference (model.HiddenState × History))
    (property : Store final → Prop)
    (all : ∀ value, 0 < ((second.execute environment Reference
      (first.execute environment Reference state)).block value).mass → property value.1)
    (value : Store final × (model.HiddenState × (History × (first.seq second).Path)))
    (positive : 0 < (((first.seq second).execute environment Reference state).block value).mass) :
    property value.1 := by
  rw [execute_seq] at positive
  exact State.supported_store_mapHistory
    (second.execute environment Reference (first.execute environment Reference state))
    (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))
    property all value positive

end
end QuantumAlg.Circuit
