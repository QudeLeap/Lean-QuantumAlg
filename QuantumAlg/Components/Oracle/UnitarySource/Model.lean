/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Oracle.Model
public import QuantumAlg.Components.Control
import all QuantumAlg.Core.Base.Oracle.Model
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Components.Control

/-!
# Explicit source-unitary access capabilities

The declaration fixes the source width and independently grants controlled,
inverse, and controlled-inverse access. The execution environment supplies the
unitary interpretation. Each nonordinary query carries its own grant; neither
ordinary access nor a combination of other grants supplies it.
The controlled query is the operation used in the Hadamard test
[AJL06, qf2.tex:635-642] and QPE [Lin22, phaseestimation.tex:514-523].
-/

namespace QuantumAlg.UnitarySource

noncomputable section

/-- Every source access form has a separate query coordinate. -/
public inductive Coordinate where
  | ordinary
  | controlled
  | inverse
  | controlledInverse
  deriving DecidableEq

/-- Each nonordinary access form requires its own explicit grant. -/
public inductive Query (allowControlled : Bool) (allowInverse : Bool := false)
    (allowControlledInverse : Bool := false) where
  | ordinary
  | controlled (granted : allowControlled = true)
  | inverse (granted : allowInverse = true)
  | controlledInverse (granted : allowControlledInverse = true)

/-- Fixed source dimensions and independent grants, without a source operator in the syntax. -/
@[expose, implicit_reducible]
public def model (width : Nat)
    (allowControlled : Bool := false) (allowInverse : Bool := false)
    (allowControlledInverse : Bool := false) : OracleModel where
  Query := Query allowControlled allowInverse allowControlledInverse
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature query := match query with
    | .ordinary | .inverse _ => QuantumSignature.qubits width
    | .controlled _ | .controlledInverse _ => QuantumSignature.qubits (1 + width)
  coordinate query := match query with
    | .ordinary => .ordinary
    | .controlled _ => .controlled
    | .inverse _ => .inverse
    | .controlledInverse _ => .controlledInverse

/-- Interpret the granted source forms consistently with one mathematical unitary. -/
@[expose]
public def interpretation {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (allowControlled : Bool := false) (allowInverse : Bool := false)
    (allowControlledInverse : Bool := false) :
    (model width allowControlled allowInverse allowControlledInverse).Interpretation where
  operator query := match query with
    | .ordinary =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm unitary
    | .controlled _ =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
          (UnitaryOperator.controlledQubits unitary)
    | .inverse _ =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm unitary⁻¹
    | .controlledInverse _ =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
          (UnitaryOperator.controlledQubits unitary⁻¹)

/-- A declaration with all optional grants disabled contains only ordinary access. -/
public lemma unitarySource_disabled_query_ordinary (query : Query false) :
    query = .ordinary := by
  cases query with
  | ordinary => rfl
  | controlled granted => cases granted
  | inverse granted => cases granted
  | controlledInverse granted => cases granted

/-- Ordinary inverse access returns exactly the adjoint of the declared source. -/
public lemma unitarySource_inverse_operator {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) (controlled controlledInverse : Bool) :
    (interpretation unitary controlled true controlledInverse).operator (.inverse rfl) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm unitary⁻¹ := rfl

/-- Control and inverse grants together still do not grant controlled-inverse access. -/
public lemma unitarySource_control_inverse_no_controlledInverse
    (width : Nat) (query : Query true true false) :
    (model width true true false).coordinate query ≠ Coordinate.controlledInverse := by
  cases query with
  | ordinary => change Coordinate.ordinary ≠ Coordinate.controlledInverse; decide
  | controlled _ => change Coordinate.controlled ≠ Coordinate.controlledInverse; decide
  | inverse _ => change Coordinate.inverse ≠ Coordinate.controlledInverse; decide
  | controlledInverse granted => cases granted

/-- Enabling control still keeps its accounting coordinate distinct from the ordinary query. -/
public lemma unitarySource_query_coordinates_distinct (width : Nat) :
    (model width true).coordinate .ordinary ≠
      (model width true).coordinate (.controlled rfl) := by
  change Coordinate.ordinary ≠ Coordinate.controlled
  decide

end

end QuantumAlg.UnitarySource
