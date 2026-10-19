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

The public instance fixes the query signature. Its source operator belongs to
a separate interpretation. An actual query chooses only its placement; no
controlled or inverse grant is added.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Ordinary opaque group action is the sole granted query coordinate. -/
public inductive Coordinate where
  | groupAction
  deriving DecidableEq

/-- The public instance fixes the complete identity-inclusive query signature. -/
@[expose, implicit_reducible]
public def model (I : ECDLPInstance E) : OracleModel where
  Query := Unit
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature _ := QuantumSignature.qubits (Layout.totalQubits I)
  coordinate _ := .groupAction

/-- A legal source operator interprets the fixed query signature. -/
@[expose] public def interpretation (I : ECDLPInstance E) (A : Access I) :
    (model I).Interpretation where
  operator _ :=
    UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm
      A.operator

/-- Canonical physical qubits of both exponents and the existing point bank. -/
public abbrev layout (I : ECDLPInstance E) : QuantumLayout (Layout.totalQubits I) :=
  (QuantumSignature.qubits (Layout.totalQubits I)).canonicalPlacement.layout

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
