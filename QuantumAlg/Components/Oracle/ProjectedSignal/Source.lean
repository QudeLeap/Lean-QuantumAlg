/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.ProjectedSignal
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Components.Oracle.ProjectedSignal
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Ordinary and inverse projected-signal queries

The projected-signal contract explicitly grants both U and its inverse. Executing
one of them preserves its own accounting coordinate; neither is a controlled query.
-/

namespace QuantumAlg.ProjectedSignal.Source

noncomputable section

variable (gates : GateModel) {width : Nat} (U : UnitaryOperator (Qubits width))
  (left right : OrthogonalProjector width) (allowControlled : Bool)

/-- Execute exactly the ordinary or inverse query on the complete source word. -/
def circuit (inverse : Bool) :
    UnitaryCircuit gates (model U left right allowControlled)
      (QuantumSignature.qubits width).canonicalPlacement.layout :=
  if inverse then
    .query (OracleModel.Application.onPlacement (model U left right allowControlled)
      (.source (.inverse rfl)) (QuantumSignature.qubits width).canonicalPlacement)
  else
    .query (OracleModel.Application.onPlacement (model U left right allowControlled)
      (.source .ordinary) (QuantumSignature.qubits width).canonicalPlacement)

/-- The complete operator is the independently declared ordinary or inverse source. -/
theorem circuit_matrix (inverse : Bool) :
    (circuit gates U left right allowControlled inverse).binaryMatrix =
      if inverse then U⁻¹ else U := by
  cases inverse <;>
    simp only [circuit, Bool.false_eq_true, ↓reduceIte, UnitaryCircuit.binaryMatrix,
      UnitaryCircuit.query_matrix, OracleModel.Application.queryApplication_onPlacement_operator]
  · change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width)
      (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm U) = _
    exact UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv width).symm _
  · change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width)
      (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm U⁻¹) = _
    exact UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv width).symm _

/-- The same actual query selects the ordinary or inverse resource coordinate. -/
theorem circuit_events (inverse : Bool) :
    (circuit gates U left right allowControlled inverse).eventCost =
      ResourcePool.singleton (model := .quantum gates (model U left right allowControlled))
        (.oracle (.source (if inverse then .inverse else .ordinary))) := by
  cases inverse <;> rfl

/-- One source query occupies one abstract dependency step. -/
theorem circuit_depth (inverse : Bool) :
    (circuit gates U left right allowControlled inverse).evaluatedEventDepth (fun _ => 1) = 1 := by
  cases inverse <;> rfl

end

end QuantumAlg.ProjectedSignal.Source
