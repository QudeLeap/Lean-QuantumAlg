/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint.Trace

/-! # Exact reversal of the default oracle-free native trace -/

namespace QuantumAlg.AlgorithmGate

noncomputable section

/-- Every inverse default instruction retains its native coordinate in reversed execution order. -/
public lemma oracleFreeAdjoints_eventTrace {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit model .empty layout) :
    (circuit.dagger (oracleFreeAdjoints .empty)).eventTrace = circuit.eventTrace.reverse := by
  apply UnitaryCircuit.dagger_eventTrace_of_singletons
  · intro count layout application
    change (UnitaryCircuit.native (oracles := .empty)
      (adjointApplication application)).eventTrace = _
    rw [UnitaryCircuit.native_eventTrace, algorithmGate_adjointApplication_coordinate]
  · intro count layout application
    exact False.elim
      (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

end

end QuantumAlg.AlgorithmGate
