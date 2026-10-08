/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Core.Execution.Interpret

/-!
# Classical-language independence of one physical reset

The actual one-wire reset contains measurement, stored-result selection and a
native quantum correction. Selecting an additional classical operation model
does not change this circuit's state transformation or its path record.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

/-- The same paid measurement and correction execute identically in every
classical operation model with the same quantum and service grants. -/
theorem circuit_execute_operationModel {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (operations : ClassicalOpModel) {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum gates oracles).HiddenState × History)) :
    (circuit wire output realizations operations).execute Reference state =
      (circuit wire output realizations).execute Reference state := by
  rfl

end

end QuantumAlg.ZReset
