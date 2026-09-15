/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Run

/-!
# The original exponent observable through actual terminal cell allocation

Allocating the retained terminal cells preserves every original quantum wire
and its basis value. The true exponent event therefore has the same weight on
the complete quantum-reference density before and after this allocation. This
identity applies to arbitrary mixed and subnormalized states, including zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP

/-- Actual terminal allocation leaves the original complete quantum event weight unchanged. -/
theorem exponentMeasurementEffect_reindex (modulus exponentWidth : Nat)
    (Reference : Register) (event : (Fin (2 * exponentWidth) → Bool) → Bool)
    (state : DensityOperator
      (Register.prod (after modulus.size (2 * exponentWidth)).register Reference)) :
    (QubitReadouts.eventEffect (exponentMeasurementWires modulus exponentWidth)
      event Reference).weight
        (state.reindex (MeasurementCells.jointBasisEquiv _ 2 (2 * exponentWidth) Reference)) =
      (QubitReadouts.eventEffect (afterExponentWires modulus exponentWidth)
        event Reference).weight state := by
  unfold exponentMeasurementWires exponentMeasurementContext
  rw [QubitReadouts.eventEffect_weight, QubitReadouts.eventEffect_weight]
  apply congrArg Complex.re
  let equivalence :
      (Register.prod (after modulus.size (2 * exponentWidth)).register Reference).Index ≃
        (Register.prod
          (MeasurementCells.context (after modulus.size (2 * exponentWidth))
            2 (2 * exponentWidth)).register Reference).Index :=
    MeasurementCells.jointBasisEquiv
      (after modulus.size (2 * exponentWidth)) 2 (2 * exponentWidth) Reference
  refine (equivalence.sum_comp _).symm.trans ?_
  apply Finset.sum_congr rfl
  intro basis _
  rw [DensityOperator.reindex_entry, Equiv.symm_apply_apply]
  change (if (event fun index => decide
    ((MeasurementCells.basisEquiv (after modulus.size (2 * exponentWidth)) 2
      (2 * exponentWidth) basis.1
        (MeasurementCells.wireEquiv (after modulus.size (2 * exponentWidth)) 2
          (2 * exponentWidth) (afterExponentWires modulus exponentWidth index))).val = 1)) =
        true then state.matrix basis basis else 0) = _
  simp only [MeasurementCells.basisEquiv_value]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The prescribed actual-run event is exactly the original-wire event after inverse Fourier. -/
theorem exponentRunDensity_eventWeight (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (Reference : Register)
    (input : DensityOperator
      (Register.prod (before p.size (2 * orderWidth problem)).register Reference))
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool) :
    (QubitReadouts.eventEffect (exponentMeasurementWires p (orderWidth problem))
      event Reference).weight
        (exponentRunDensity E fieldTail odd problem points Reference input) =
      (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem))
        event Reference).weight
          (preMeasurementDensity E fieldTail odd problem points Reference input) :=
  exponentMeasurementEffect_reindex p (orderWidth problem) Reference event _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
