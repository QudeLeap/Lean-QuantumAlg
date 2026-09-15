/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Born
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Probability
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Amplification.Model

/-!
# Original selected-family floor for the literal native ECDLP sampler

The actual sampler has the original concrete Born law. Its unchanged
unit-indexed selected family therefore has the original positive floor and
failure complement. The secret is only the existing mathematical witness;
no success, seed, or reference-state certificate enters the actual program.
This probability transfer does not transfer analytical preparation costs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

noncomputable section

open FiniteCyclicDLP.Concrete.Amplification

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Each original selected frequency has its original pointwise floor in the actual Born law. -/
theorem nativeECDLP_selectedOutcome_probability_ge
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I)
    (unit : (ZMod (problem I).order)ˣ) :
    FiniteCyclicDLP.Probability.selectedOutcomePointwiseLowerBound (problem I) ≤
      outcomePMF I B A
        (FiniteCyclicDLP.Probability.selectedOutcome (problem I) (input I) unit) := by
  rw [nativeECDLP_outcomePMF_eq_concrete]
  exact FiniteCyclicDLP.Concrete.Probability.selectedOutcomePointwiseLowerBound_le_bornProbability
    (input I) (circuitAccess I A) unit

/-- The complete original selected family has its unchanged floor in the actual Born law. -/
theorem nativeECDLP_selectedFamily_probability_ge
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) :
    FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound (problem I) ≤
      (outcomePMF I B A).toOuterMeasure
        {outcome | outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I)
          (input I)} := by
  rw [nativeECDLP_outcomePMF_eq_concrete]
  exact
    FiniteCyclicDLP.Concrete.Probability.selectedOutcomeFamilyLowerBound_le_bornSelectedProbability
      (input I) (circuitAccess I A)

/-- The complement of the actual selected-event mass obeys the original retry failure budget. -/
theorem nativeECDLP_selectedFailure_probability_le
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) :
    1 - (outcomePMF I B A).toOuterMeasure
        {outcome | outcome ∈ FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I)
          (input I)} ≤
      ENNReal.ofReal
        (FiniteCyclicDLP.Concrete.Amplification.sourceFailureBudget (problem I)).value := by
  calc
    _ ≤ 1 - FiniteCyclicDLP.Probability.selectedOutcomeFamilyLowerBound (problem I) :=
      tsub_le_tsub_left (nativeECDLP_selectedFamily_probability_ge I B A) 1
    _ = _ :=
      one_sub_selectedOutcomeFamilyLowerBound_eq_sourceFailure (problem I)

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
