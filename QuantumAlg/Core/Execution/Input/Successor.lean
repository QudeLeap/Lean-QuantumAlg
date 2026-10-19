/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Input.Oracle
public import QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Interpret

/-!
# Actual successor inputs

Project only mathematical path histories from a complete normalized execution.
The physical store, persistent services and quantum-reference state survive.
-/

namespace QuantumAlg.Circuit

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual normalized prefix output, retaining its live store, persistent
service state and quantum/reference correlations. Only mathematical histories
are summed away; no service initialization or physical reset is performed. -/
public def nextInput {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool} (code : Circuit model pre post allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) :
    Execution.OracleInput model.classicalOracles post Reference where
  state := (code.execute environment Reference
    (input.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))).mapClassical
      (fun record => (record.1, record.2.1))
  normalized := (ExecutionState.mapClassical_mass _ _).trans
    ((code.execute_mass environment Reference _).trans
      ((input.state.mapClassical_mass _).trans input.normalized))

end

end QuantumAlg.Circuit
