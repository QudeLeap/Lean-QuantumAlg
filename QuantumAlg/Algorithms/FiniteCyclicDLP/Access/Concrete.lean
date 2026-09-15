/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Unitary
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Unitary

/-!
# Original encoded group query on the concrete finite-cyclic bank

The original group encoding occupies the same third Fourier-width register.
Its given basis action supplies the concrete experiment without restricting
the group or replacing the original counted oracle by a gate implementation.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The original encoded group action, with the literal preparation witness
used only to instantiate the existing unitary query declaration. -/
def circuitAccess (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    ConcreteCircuitAccess P where
  Tail := Fin (2 ^ orderWidth P)
  tailEncoding := BinaryLabelEncoding.finIdentity (orderWidth P)
  cleanTail := ux.encode
  cleanTail_injective := ux.encode_injective
  oracleCircuit := uxCircuit (GateLevelAttempt.derivedAccess P B ux)
  oracleCircuit_physical_idx := uxCircuit_physical_idx _
  realizesClean := by
    intro left right workspace
    change ux.operator.apply
        (NormalizedVector.ket (R := Qubits (totalQubits P))
          (tripleIndex left right (ux.encode workspace))) =
      NormalizedVector.ket (R := Qubits (totalQubits P))
        (tripleIndex left right
          (ux.encode (workspace *
            P.toSourceScope.oracleMultiplier left.val right.val)))
    exact ux.basisAction left right workspace

end

end QuantumAlg.FiniteCyclicDLP.Canonical
