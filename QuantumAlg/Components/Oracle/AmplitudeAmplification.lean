/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Oracle.Model
public import QuantumAlg.Components.Control
public import QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Core.Base.Oracle.Model
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Oracle.Reflection

/-!
# Explicit source access for amplitude amplification

The source provides preparation and good-state reflection
[Lin22, grover.tex:290-319]. Using the inverse preparation or a coherently
controlled good reflection requires its own declared grant. The known
all-zero reflection is implemented by native gates, not included as a query.
No query below supplies controlled preparation or an arbitrary unitary.
-/

namespace QuantumAlg.AmplitudeAmplificationSource

noncomputable section

/-- Each distinct source access form has its own accounting coordinate. -/
public inductive Coordinate where
  | preparation
  | inversePreparation
  | goodReflection
  | controlledGoodReflection
  deriving DecidableEq

/-- Inverse and coherent-control access require evidence of the corresponding grant. -/
public inductive Query (allowInverse allowControlledGood : Bool) where
  | preparation
  | inversePreparation (granted : allowInverse = true)
  | goodReflection
  | controlledGoodReflection (granted : allowControlledGood = true)

/-- The Problem selects this fixed source and its explicit inverse/control access forms. -/
@[expose, implicit_reducible]
public def model {width : Nat} (preparation : UnitaryOperator (Qubits width))
    (good : NormalizedVector (Qubits width))
    (allowInverse allowControlledGood : Bool) : OracleModel where
  Query := Query allowInverse allowControlledGood
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature query := match query with
    | .preparation | .inversePreparation _ | .goodReflection => QuantumSignature.qubits width
    | .controlledGoodReflection _ => QuantumSignature.qubits (1 + width)
  operator query := match query with
    | .preparation =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm preparation
    | .inversePreparation _ =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm (star preparation)
    | .goodReflection =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm
          (OrthogonalProjector.rankOnePhaseReflectionOp good)
    | .controlledGoodReflection _ =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
          (UnitaryOperator.controlledQubits (OrthogonalProjector.rankOnePhaseReflectionOp good))
  coordinate query := match query with
    | .preparation => .preparation
    | .inversePreparation _ => .inversePreparation
    | .goodReflection => .goodReflection
    | .controlledGoodReflection _ => .controlledGoodReflection

/-- Without either grant, only ordinary preparation and good reflection can be called. -/
public theorem amplitudeSource_ungranted_queries (query : Query false false) :
    query = .preparation ∨ query = .goodReflection := by
  cases query with
  | preparation => exact Or.inl rfl
  | goodReflection => exact Or.inr rfl
  | inversePreparation granted => cases granted
  | controlledGoodReflection granted => cases granted

/-- Ordinary preparation and its explicitly granted inverse remain separate query counts. -/
public theorem amplitudeSource_inverse_coordinate_distinct {width : Nat}
    (preparation : UnitaryOperator (Qubits width)) (good : NormalizedVector (Qubits width))
    (controlled : Bool) :
    (model preparation good true controlled).coordinate .preparation ≠
      (model preparation good true controlled).coordinate (.inversePreparation rfl) := by
  change Coordinate.preparation ≠ Coordinate.inversePreparation
  decide

/-- Granting coherent reflection does not merge it with the ordinary reflection coordinate. -/
public theorem amplitudeSource_controlled_coordinate_distinct {width : Nat}
    (preparation : UnitaryOperator (Qubits width)) (good : NormalizedVector (Qubits width))
    (inverse : Bool) :
    (model preparation good inverse true).coordinate .goodReflection ≠
      (model preparation good inverse true).coordinate (.controlledGoodReflection rfl) := by
  change Coordinate.goodReflection ≠ Coordinate.controlledGoodReflection
  decide

end

end QuantumAlg.AmplitudeAmplificationSource
