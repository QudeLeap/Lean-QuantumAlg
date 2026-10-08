/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Specification
public import QuantumAlg.Core.Base.Oracle.Model
public import QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# The fixed declared ECDLP query model

The original intrinsic operator and signature belong to this model. An actual
query chooses only its placement; no controlled or inverse grant is added.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Ordinary opaque group action is the sole granted query coordinate. -/
public inductive Coordinate where
  | groupAction
  deriving DecidableEq

/-- Fix the original operator and the complete identity-inclusive signature once. -/
@[expose, implicit_reducible]
public def model (I : ECDLPInstance E) (A : Access I) : OracleModel where
  Query := Unit
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature _ := QuantumSignature.qubits (Layout.totalQubits I)
  operator _ :=
    UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm
      A.operator
  coordinate _ := .groupAction

/-- Canonical physical qubits of both exponents and the existing point bank. -/
public abbrev layout (I : ECDLPInstance E) : QuantumLayout (Layout.totalQubits I) :=
  (QuantumSignature.qubits (Layout.totalQubits I)).canonicalPlacement.layout

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
