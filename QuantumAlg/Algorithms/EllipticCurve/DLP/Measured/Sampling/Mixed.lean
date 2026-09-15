/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Comparison
import all QuantumAlg.Core.Execution.Circuit.FixedBasis

/-!
# The original sampling floor for every actual mixed fixed-basis input

Every old Store and reference correlation is retained. The original local
sampling basis is the only quantum support condition, to be established by
actual initialization or reset. Uniform pure-reference bounds extend to
the complete input's original mass, with the original exceptional error.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding MAU.Inversion.SharedEEA
open FiniteCyclicDLP Canonical.Probability

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual sampling prefix retains the original floor for arbitrary mixed conditional inputs. -/
theorem selectedSamplingPrefix_mixed_weight_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem) {Reference : Register} {H : Type} [Fintype H]
    (state : State (after p.size (2 * orderWidth problem)) Reference H)
    (support : ∀ basis :
        ((after p.size (2 * orderWidth problem)).register.prod Reference).Index,
      basis.1 ≠ initializedAssembly p (2 * orderWidth problem)
        ((BasisPreparation.zero (indexedLayout p.size (2 * orderWidth problem))).value,
          (InPlacePreparation.preparation p).value,
          pairedMontgomeryInput fieldTail (orderWidth problem) sameWidth fits seed (0, 0)) →
        state.quantumMarginal.matrix basis basis = 0) :
    state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
          4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem))
        (selectedExponentEvent problem input) Reference).weight
        (((samplingPrefix E fieldTail odd problem points).execute Reference
          state).quantumMarginal) := by
  apply Circuit.observedWeight_lower_of_fixedBasis (samplingPrefix E fieldTail odd problem points)
    Reference
    (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem))
      (selectedExponentEvent problem input) Reference)
    (initializedAssembly p (2 * orderWidth problem)
      ((BasisPreparation.zero (indexedLayout p.size (2 * orderWidth problem))).value,
        (InPlacePreparation.preparation p).value,
        pairedMontgomeryInput fieldTail (orderWidth problem) sameWidth fits seed (0, 0)))
    (samplingInputVector problem fieldTail sameWidth fits seed)
    (samplingInputVector_entry problem fieldTail sameWidth fits seed)
  · intro store reference
    have pure := selectedSamplingPrefix_weight_bound E fieldTail sameWidth fits odd problem
      points seed addends input reference store
    linarith
  · exact support

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
