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

A source occurrence fixes its query and coordinate through the selected
oracle interface. The execution environment supplies the operator. Placement supplies only the
  actual physical wires. Inverse and
controlled calls consume the grant evidence required by that model.
-/

namespace QuantumAlg.UnitarySource.Circuit

noncomputable section

variable (gates : GateModel) (width : Nat)
  (allowControlled allowInverse allowControlledInverse : Bool)

/-- Execute one available source instance at its complete dimension-correct placement. -/
def program (query : Query allowControlled allowInverse allowControlledInverse)
    (placement :
      ((model width allowControlled allowInverse allowControlledInverse).signature
        query).Placement) :
    UnitaryCircuit gates (model width allowControlled allowInverse allowControlledInverse)
      placement.layout :=
  .query (OracleModel.Application.onPlacement
    (model width allowControlled allowInverse allowControlledInverse) query placement)

/-- The selected interpretation is transported through the fixed physical query placement. -/
lemma program_matrix
    (environment : (model width allowControlled allowInverse allowControlledInverse).Interpretation)
    (query : Query allowControlled allowInverse allowControlledInverse)
    (placement :
      ((model width allowControlled allowInverse allowControlledInverse).signature
        query).Placement) :
    (program gates width allowControlled allowInverse allowControlledInverse query
      placement).matrix environment =
      UnitaryOperator.reindex placement.indexEquiv.symm
        (environment.operator query) := by
  rw [program, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  rfl

/-- One actual call contributes exactly its declared coordinate to the query ledger. -/
lemma program_eventCost (query : Query allowControlled allowInverse allowControlledInverse)
    (placement :
      ((model width allowControlled allowInverse allowControlledInverse).signature
        query).Placement) :
    (program gates width allowControlled allowInverse allowControlledInverse
      query placement).eventCost =
      ResourcePool.singleton
        (model := .quantum gates (model width allowControlled allowInverse allowControlledInverse))
        (.oracle
          ((model width allowControlled allowInverse allowControlledInverse).coordinate query))
            := rfl

/-- One granted source query occupies one abstract dependency step. -/
lemma program_unitDepth (query : Query allowControlled allowInverse allowControlledInverse)
    (placement :
      ((model width allowControlled allowInverse allowControlledInverse).signature
        query).Placement) :
    (program gates width allowControlled allowInverse allowControlledInverse
      query placement).evaluatedEventDepth (fun _ => 1) = 1 := rfl

end

end QuantumAlg.UnitarySource.Circuit
