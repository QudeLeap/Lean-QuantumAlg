/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.UnitarySource.Model
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Oracle.UnitarySource.Model
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit

/-!
# Actual granted source-unitary queries

A source occurrence fixes its operator and coordinate through the selected
oracle model. Placement supplies only the actual physical wires. Inverse and
controlled calls consume the grant evidence required by that model.
-/

namespace QuantumAlg.UnitarySource.Circuit

noncomputable section

variable (gates : GateModel) {width : Nat}
  (U : UnitaryOperator (Qubits width))
  (allowControlled allowInverse allowControlledInverse : Bool)

/-- Execute one available source instance at its complete dimension-correct placement. -/
def program (query : Query allowControlled allowInverse allowControlledInverse)
    (placement :
      ((model U allowControlled allowInverse allowControlledInverse).signature query).Placement) :
    UnitaryCircuit gates (model U allowControlled allowInverse allowControlledInverse)
      placement.layout :=
  .query (OracleModel.Application.onPlacement
    (model U allowControlled allowInverse allowControlledInverse) query placement)

/-- The complete matrix is fixed by the declared query, with exact physical coordinate transport. -/
theorem program_matrix (query : Query allowControlled allowInverse allowControlledInverse)
    (placement :
      ((model U allowControlled allowInverse allowControlledInverse).signature query).Placement) :
    (program gates U allowControlled allowInverse allowControlledInverse query placement).matrix =
      UnitaryOperator.reindex placement.indexEquiv.symm
        ((model U allowControlled allowInverse allowControlledInverse).operator query) := by
  rw [program, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  rfl

/-- One actual call contributes exactly its declared coordinate to the query ledger. -/
theorem program_eventCost (query : Query allowControlled allowInverse allowControlledInverse)
    (placement :
      ((model U allowControlled allowInverse allowControlledInverse).signature query).Placement) :
    (program gates U allowControlled allowInverse allowControlledInverse
      query placement).eventCost =
      ResourcePool.singleton
        (model := .quantum gates (model U allowControlled allowInverse allowControlledInverse))
        (.oracle
          ((model U allowControlled allowInverse allowControlledInverse).coordinate query)) := rfl

/-- One granted source query occupies one abstract dependency step. -/
theorem program_unitDepth (query : Query allowControlled allowInverse allowControlledInverse)
    (placement :
      ((model U allowControlled allowInverse allowControlledInverse).signature query).Placement) :
    (program gates U allowControlled allowInverse allowControlledInverse
      query placement).evaluatedEventDepth (fun _ => 1) = 1 := rfl

end

end QuantumAlg.UnitarySource.Circuit
