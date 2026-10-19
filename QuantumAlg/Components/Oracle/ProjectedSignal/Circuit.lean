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
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Actual declared projector queries

The complete phase-and-source word is the signature of each projector-controlled
NOT. Placement changes neither the declared projector nor its query coordinate.
-/

namespace QuantumAlg.ProjectedSignal.Circuit

noncomputable section

variable (gates : GateModel) (width : Nat) (allowControlled : Bool)

/-- Select the right projector when true, otherwise the left projector. -/
def projectorFlip (useRight : Bool) :
    UnitaryCircuit gates (model width allowControlled)
      (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout :=
  if useRight then
    .query (OracleModel.Application.onPlacement (model width allowControlled) .rightNot
      (QuantumSignature.qubits (1 + width)).canonicalPlacement)
  else
    .query (OracleModel.Application.onPlacement (model width allowControlled) .leftNot
      (QuantumSignature.qubits (1 + width)).canonicalPlacement)

/-- The query's complete binary matrix is exactly the fixed projector-controlled NOT. -/
lemma projectorFlip_matrix (U : UnitaryOperator (Qubits width))
    (left right : OrthogonalProjector width) (useRight : Bool) :
    (projectorFlip gates width allowControlled useRight).binaryMatrix
      (interpretation U left right allowControlled) =
      OrthogonalProjector.controlledNotOp (if useRight then right else left) := by
  cases useRight <;>
    simp only [projectorFlip, Bool.false_eq_true, ↓reduceIte,
      UnitaryCircuit.binaryMatrix, UnitaryCircuit.query_matrix,
      OracleModel.Application.queryApplication_onPlacement_operator]
  · change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width))
      (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
        (OrthogonalProjector.controlledNotOp left)) = _
    exact UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv (1 + width)).symm _
  · change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width))
      (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
        (OrthogonalProjector.controlledNotOp right)) = _
    exact UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv (1 + width)).symm _

/-- Every projector call emits exactly its own declared query coordinate. -/
lemma projectorFlip_events (useRight : Bool) :
    (projectorFlip gates width allowControlled useRight).eventCost =
      ResourcePool.singleton (model := .quantum gates (model width allowControlled))
        (.oracle (if useRight then Coordinate.rightNot else Coordinate.leftNot)) := by
  cases useRight <;> rfl

/-- A projector query occupies one abstract dependency step. -/
lemma projectorFlip_depth (useRight : Bool) :
    (projectorFlip gates width allowControlled useRight).evaluatedEventDepth (fun _ => 1) =
      1 := by
  cases useRight <;> rfl

end

end QuantumAlg.ProjectedSignal.Circuit
