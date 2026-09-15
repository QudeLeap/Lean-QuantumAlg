/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.HiddenLine

/-!
# Original prime-order specialization of the finite-cyclic Born floor

The source probability theorem consumes the original circuit and retains its
original scope. Numeric retry calibration has a separate dependency owner.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- For a prime-order problem, one canonical attempt assigns at least
`r(r-1)/(4q²)` to the selected raw-outcome family. -/
theorem primeOrderFloor_le_probability (P : KnownOrderProblem G)
    (input : Probability.SecretInput P) (A : Access P)
    (hprime : P.order.Prime) :
    ENNReal.ofReal
        (((P.order * (P.order - 1) : Nat) : Real) /
          successDenominator P) ≤
      ((terminalMeasurement P).outcomePMF
        (BornBridge.evolvedState A)).toOuterMeasure
        {outcome | Probability.SelectedRawOutcome P input outcome} := by
  rw [← attemptFloor_eq_primeOrder P hprime,
    ← selectedRawOutcomeFamilyLowerBound_eq_ofReal_attemptFloor P]
  exact Probability.selectedRawOutcomeFamilyLowerBound_le_probability P input A

end

end QuantumAlg.FiniteCyclicDLP.Canonical
