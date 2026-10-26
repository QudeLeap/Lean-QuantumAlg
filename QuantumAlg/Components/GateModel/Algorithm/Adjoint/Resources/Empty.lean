/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-! # Exact resources of actual native adjoints in the same query-free model -/

namespace QuantumAlg.AlgorithmGate

noncomputable section

private lemma oracleFreeEvent_empty (event : Resource.Event (.quantum model .empty)) :
    oracleFreeEvent .empty event = event := by
  cases event with
  | classicalOperation impossible => nomatch impossible
  | classicalQuery impossible => nomatch impossible
  | gate => rfl
  | oracle impossible => nomatch impossible
  | preparation => rfl
  | measurement => rfl

/-- Including the empty query alphabet retains every identical actual event coordinate. -/
lemma oracleFreePool_empty (pool : ResourcePool (.quantum model .empty)) :
    oracleFreePool .empty pool = pool := by
  change Multiset.map (oracleFreeEvent .empty) pool = pool
  have identity : oracleFreeEvent .empty = id := funext oracleFreeEvent_empty
  rw [identity, Multiset.map_id]

/-- The same-model actual native adjoint has exactly the entire source event ledger. -/
lemma algorithmGate_emptyAdjoints_eventCost {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit model .empty layout) :
    (circuit.dagger (oracleFreeAdjoints .empty)).eventCost = circuit.eventCost := by
  rw [algorithmGate_oracleFreeAdjoints_eventCost, oracleFreePool_empty]

/-- Real native inversion retains the actual source dependency schedule in default quantum time. -/
lemma algorithmGate_emptyAdjoints_quantumTime {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit model .empty layout) :
    (circuit.dagger (oracleFreeAdjoints .empty)).evaluatedEventDepth
        Resource.Event.quantumDuration =
      circuit.evaluatedEventDepth Resource.Event.quantumDuration := by
  have inverse := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (circuit.dagger (oracleFreeAdjoints .empty)) .empty .empty
  have forward := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth circuit .empty .empty
  exact inverse.trans
    ((algorithmGate_oracleFreeAdjoints_unit_depth .empty circuit).trans forward.symm)

end

end QuantumAlg.AlgorithmGate
