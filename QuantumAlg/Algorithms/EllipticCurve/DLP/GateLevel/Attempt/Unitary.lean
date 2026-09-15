/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Unitary
import all QuantumAlg.Algorithms.EllipticCurve.DLP.OrderPreparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Access

/-!
# Literal elliptic-curve discrete-logarithm unitary attempt

The source order expansion prepares both exponent registers, including its
one-term power-of-two case. The identity-inclusive point register is retained
through the single opaque group query and the two inverse QFTs.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ECDLP
namespace Canonical
namespace GateLevelAttempt

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Two literal order preparations on the exponent registers. -/
def exponentPreparationCircuit (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) :
    UnitaryCircuit (Qubits
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))) :=
  FiniteCyclicDLP.Canonical.pairConsecutiveCircuit
    (B.paddedPreparation (problem I))
    (B.paddedPreparation_physical_idx (problem I))

@[simp]
theorem exponentPreparationCircuit_physical_idx (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) :
    (exponentPreparationCircuit I B).physical_idx =
      List.range
        (FiniteCyclicDLP.orderWidth (problem I) +
          FiniteCyclicDLP.orderWidth (problem I)) :=
  FiniteCyclicDLP.Canonical.pairConsecutiveCircuit_physical_idx
    (B.paddedPreparation (problem I))
    (B.paddedPreparation_physical_idx (problem I))

/-- The two explicit preparations extended by the untouched intrinsic point
register. -/
def preparationCircuit (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) :
    UnitaryCircuit (Qubits (Layout.totalQubits I)) :=
  extendWithPoint I (exponentPreparationCircuit I B)
    (exponentPreparationCircuit_physical_idx I B)

@[simp]
theorem preparationCircuit_physical_idx (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) :
    (preparationCircuit I B).physical_idx = List.range (Layout.totalQubits I) :=
  extendWithPoint_physical_idx I _ _

@[simp]
theorem preparationCircuit_eventCost (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) :
    (preparationCircuit I B).eventCost =
      (B.paddedPreparation (problem I)).eventCost +
        (B.paddedPreparation (problem I)).eventCost := by
  rw [preparationCircuit, extendWithPoint_eventCost]
  exact FiniteCyclicDLP.Canonical.pairConsecutiveCircuit_eventCost
    (B.paddedPreparation (problem I))
      (B.paddedPreparation_physical_idx (problem I))

/-- One real preparation-query-readout circuit on the intrinsic point layout. -/
def quantumCircuit (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    UnitaryCircuit (Qubits (Layout.totalQubits I)) :=
  UnitaryCircuit.seq (preparationCircuit I B)
    (UnitaryCircuit.seq (uPQCircuit I A) (inverseQFTCircuit I))

@[simp]
theorem quantumCircuit_physical_idx (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    (quantumCircuit I B A).physical_idx = List.range (Layout.totalQubits I) := by
  simp only [quantumCircuit, UnitaryCircuit.seq, preparationCircuit_physical_idx,
    uPQCircuit_physical_idx, inverseQFTCircuit_physical_idx,
    UnitaryCircuit.unionPhysicalIdx_self]

end

end GateLevelAttempt
end Canonical
end ECDLP
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
