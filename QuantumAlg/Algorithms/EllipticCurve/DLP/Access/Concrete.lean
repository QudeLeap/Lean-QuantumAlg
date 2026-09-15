/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Unitary
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Unitary

/-!
# Original opaque ECDLP action on the concrete point bank

The intrinsic identity-inclusive point encoding and the original action of
the counted group query provide the concrete clean-tail experiment.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Package the intrinsic-layout opaque oracle into the shared real-layout
finite-cyclic circuit spine.  Unlike a gate-compiled access, this object
intentionally has no `OracleCircuitQuantumSubroutineFree` instance: its one
opaque coordinate is exactly the public `U_{P,Q}` query. -/
def circuitAccess (I : ECDLPInstance E) (A : Access I) :
    FiniteCyclicDLP.ConcreteCircuitAccess (problem I) where
  Tail := GroupPoint E
  tailEncoding := Layout.pointEncoding E
  cleanTail := id
  cleanTail_injective := Function.injective_id
  oracleCircuit := uPQCircuit I A
  oracleCircuit_physical_idx := uPQCircuit_physical_idx I A
  realizesClean := by
    intro left right workspace
    change A.operator.apply
        (NormalizedVector.ket (R := Qubits (Layout.totalQubits I))
          (basisIndex I left right workspace)) =
      NormalizedVector.ket (R := Qubits (Layout.totalQubits I))
        (basisIndex I left right
          (workspace *
            (problem I).toSourceScope.oracleMultiplier left.val right.val))
    simpa only [FiniteCyclicDLP.ConcreteCircuitAccess.encoding,
      FiniteCyclicDLP.ConcreteCircuitAccess.exponentEncoding,
      FiniteCyclicDLP.ConcreteCircuitAccess.cleanState,
      BinaryLabelEncoding.prod_encode, BinaryLabelEncoding.finIdentity_encode,
      id_eq, basisIndex, Layout.fullEncoding] using
        A.basisAction left right workspace

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
