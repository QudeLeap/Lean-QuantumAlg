/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.UnitarySource.Model
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Components.Oracle.UnitarySource.Model
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Ordinary and inverse source queries in binary coordinates

The source contract explicitly grants both U and its inverse. Executing
one of them preserves its own accounting coordinate; neither is a controlled query.
-/

namespace QuantumAlg.UnitarySource.Binary

noncomputable section

variable (gates : GateModel) (width : Nat)
  (allowControlled : Bool)

/-- Execute exactly the ordinary or inverse query on the complete source word. -/
def circuit (inverse : Bool) :
    UnitaryCircuit gates (model width allowControlled true false)
      (QuantumSignature.qubits width).canonicalPlacement.layout :=
  if inverse then
    .query (OracleModel.Application.onPlacement (model width allowControlled true false)
      (.inverse rfl) (QuantumSignature.qubits width).canonicalPlacement)
  else
    .query (OracleModel.Application.onPlacement (model width allowControlled true false)
      .ordinary (QuantumSignature.qubits width).canonicalPlacement)

/-- The complete operator is the independently declared ordinary or inverse source. -/
lemma circuit_matrix (U : UnitaryOperator (Qubits width)) (inverse : Bool) :
    (circuit gates width allowControlled inverse).binaryMatrix (interpretation U
      allowControlled true false) =
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
lemma circuit_events (inverse : Bool) :
    (circuit gates width allowControlled inverse).eventCost =
      ResourcePool.singleton (model := .quantum gates (model width allowControlled true false))
        (.oracle (if inverse then .inverse else .ordinary)) := by
  cases inverse <;> rfl

/-- One source query occupies one abstract dependency step. -/
lemma circuit_depth (inverse : Bool) :
    (circuit gates width allowControlled inverse).evaluatedEventDepth (fun _ => 1) = 1 := by
  cases inverse <;> rfl

end

end QuantumAlg.UnitarySource.Binary
