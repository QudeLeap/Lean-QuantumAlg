/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Layout
public import QuantumAlg.Core.Base
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout

/-!
# Intrinsic opaque elliptic-curve group-action contract

The operator acts on the fixed identity-inclusive point encoding and on every
encoded group point. Its declaration is independent of any execution backend.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The fixed intrinsic basis label of two exponents and one actual curve
point. -/
public def basisIndex (I : ECDLPInstance E)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (workspace : GroupPoint E) : Fin (2 ^ Layout.totalQubits I) :=
  (Layout.fullEncoding I).encode ((left, right), workspace)

/-- Opaque `U_{P,Q}` access on the intrinsic identity-inclusive point layout.
No encoding or width is supplied by the caller. -/
public structure Access (I : ECDLPInstance E) where
  /-- The certified black-box group-action unitary. -/
  operator : UnitaryOperator (Qubits (Layout.totalQubits I))
  /-- Source-faithful action on every canonical point-register basis state. -/
  basisAction :
    ∀ (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
      (workspace : GroupPoint E),
      operator.apply
          (NormalizedVector.ket (R := Qubits (Layout.totalQubits I))
            (basisIndex I left right workspace)) =
        NormalizedVector.ket (R := Qubits (Layout.totalQubits I))
          (basisIndex I left right
            (workspace *
              (problem I).toSourceScope.oracleMultiplier left.val right.val))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
