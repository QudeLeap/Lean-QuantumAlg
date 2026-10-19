/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint.Depth
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Event
import all QuantumAlg.Core.Base.Oracle.Model
import Mathlib.Data.Multiset.MapFold

/-!
# Resources of default native adjoints without oracle access

The following inclusion is used only to state a proved ledger equation. The
actual inverse circuit is generated from one native inverse per source gate;
it never emits a query merely because the target declares oracle access.
-/

namespace QuantumAlg.AlgorithmGate

noncomputable section

/-- Include query-free event coordinates without introducing a query coordinate. -/
public def oracleFreeEvent (oracles : OracleModel) :
    Resource.Event (.quantum model .empty) → Resource.Event (.quantum model oracles)
  | .classicalOperation impossible => nomatch impossible
  | .classicalQuery impossible => nomatch impossible
  | .gate coordinate => .gate coordinate
  | .oracle impossible => nomatch impossible
  | .preparation dimension => .preparation dimension
  | .measurement dimension => .measurement dimension

/-- Additive inclusion of literal event coordinates for an oracle-free source. -/
public def oracleFreePool (oracles : OracleModel) :
    ResourcePool (.quantum model .empty) →+ ResourcePool (.quantum model oracles) where
  toFun := Multiset.map (oracleFreeEvent oracles)
  map_zero' := rfl
  map_add' := Multiset.map_add _

/-- The actual generated native inverses preserve the full query-free event ledger. -/
public lemma algorithmGate_oracleFreeAdjoints_eventCost (oracles : OracleModel)
    {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit model .empty layout) :
    (circuit.dagger (oracleFreeAdjoints oracles)).eventCost =
      oracleFreePool oracles circuit.eventCost := by
  apply UnitaryCircuit.dagger_eventCost circuit (oracleFreeAdjoints oracles)
    (oracleFreePool oracles)
  · intro count layout application
    change ResourcePool.singleton (model := .quantum model oracles)
      (.gate (adjointApplication application).coordinate) = _
    rw [algorithmGate_adjointApplication_coordinate]
    rfl
  · intro count layout application
    exact False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

/-- One native inverse per source gate preserves unit-duration dependency depth. -/
public lemma algorithmGate_oracleFreeAdjoints_unit_depth (oracles : OracleModel)
    {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit model .empty layout) :
    (circuit.dagger (oracleFreeAdjoints oracles)).evaluatedEventDepth (fun _ => 1) =
      circuit.evaluatedEventDepth (fun _ => 1) := by
  apply UnitaryCircuit.dagger_evaluatedEventDepth circuit (oracleFreeAdjoints oracles)
    (fun _ => 1) (fun _ => 1)
  · intro count layout application
    rfl
  · intro count layout application
    exact False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

end

end QuantumAlg.AlgorithmGate
