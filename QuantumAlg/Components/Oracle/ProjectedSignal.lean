/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.UnitarySource.Model
public import QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Components.Oracle.UnitarySource.Model
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Explicit projected-signal access

The projected-QSVT source supplies U, its inverse, and controlled NOTs for two
fixed projectors [GSLW19, BlockHam.tex:883-890]. Optional controlled-U access
requires an additional grant. Projector calls have their own query coordinates;
a caller cannot substitute a different projector or an arbitrary phase operator.
-/

namespace QuantumAlg.ProjectedSignal

noncomputable section

/-- Source queries and the two declared projector queries are counted separately. -/
public inductive Coordinate where
  | source (coordinate : UnitarySource.Coordinate)
  | leftNot
  | rightNot
  deriving DecidableEq

/-- Selecting this source contract grants inverse U and the two fixed projector operations. -/
public inductive Query (allowControlled : Bool) where
  | source (query : UnitarySource.Query allowControlled true false)
  | leftNot
  | rightNot

/-- The Problem fixes its source and both projectors before constructing any query. -/
@[expose, implicit_reducible]
public def model {width : Nat} (U : UnitaryOperator (Qubits width))
    (left right : OrthogonalProjector width) (allowControlled : Bool := false) : OracleModel where
  Query := Query allowControlled
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature query := match query with
    | .source query => (UnitarySource.model U allowControlled true).signature query
    | .leftNot | .rightNot => QuantumSignature.qubits (1 + width)
  operator query := match query with
    | .source query => (UnitarySource.model U allowControlled true).operator query
    | .leftNot =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
          (OrthogonalProjector.controlledNotOp left)
    | .rightNot =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
          (OrthogonalProjector.controlledNotOp right)
  coordinate query := match query with
    | .source query => .source ((UnitarySource.model U allowControlled true).coordinate query)
    | .leftNot => .leftNot
    | .rightNot => .rightNot

/-- The declared left and right capabilities remain distinct even for equal projectors. -/
public theorem projectedSignal_projector_coordinates_distinct {width : Nat}
    (U : UnitaryOperator (Qubits width)) (left right : OrthogonalProjector width)
    (allowControlled : Bool) :
    (model U left right allowControlled).coordinate .leftNot ≠
      (model U left right allowControlled).coordinate .rightNot := by
  change Coordinate.leftNot ≠ Coordinate.rightNot
  decide

/-- The inverse source query has its own coordinate and does not become a projector call. -/
public theorem projectedSignal_inverse_coordinate {width : Nat}
    (U : UnitaryOperator (Qubits width)) (left right : OrthogonalProjector width)
    (allowControlled : Bool) :
    (model U left right allowControlled).coordinate (.source (.inverse rfl)) =
      .source .inverse := rfl

end

end QuantumAlg.ProjectedSignal
