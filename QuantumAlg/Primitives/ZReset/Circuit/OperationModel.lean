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

variable {services : ClassicalOracleModel}

/-- The same paid measurement and correction execute identically in every
classical operation model with the same quantum and service grants. -/
lemma circuit_execute_operationModel {allowAllocation : Bool}
    {gates : GateModel} {oracles : OracleModel}
    {environment : (ExecutionModel.quantum gates oracles .empty services).Environment}
    {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (operations : ClassicalOpModel) {Reference : Register} {History : Type}
    [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum gates oracles .empty services).HiddenState × History)) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).execute
      ⟨environment.quantum, environment.classical⟩ Reference state =
      (circuit (allowAllocation := allowAllocation) (services := services) wire output
          realizations).execute
      ⟨environment.quantum, environment.classical⟩ Reference state := by
  rfl

end

end QuantumAlg.ZReset
