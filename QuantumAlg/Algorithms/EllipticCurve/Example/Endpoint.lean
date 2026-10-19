/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.EllipticCurve.Example.Oracle
import all QuantumAlg.Algorithms.EllipticCurve.Example.Expansion
import all QuantumAlg.Algorithms.EllipticCurve.DLP

/-!
# Typed small-curve ECDLP endpoint

The published certificate specializes the canonical budget-parametric run and
its complete declared execution and independent Algorithm.Solves problem to the fixed curve.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace Example

open PrimeFieldShortWeierstrass
open Factoring

noncomputable section

/-! ## Fixed close-to-one endpoint -/

/-- Fixed failure budget for the concrete certificate. -/
def publishedFailureBudget : FailureBudget where
  failureNumerator := 1
  failureDenominator := 100

lemma publishedFailureBudget_wellFormed :
    publishedFailureBudget.WellFormed := by
  constructor <;> norm_num [publishedFailureBudget]

/-- Retry count computed from the actual order-seven Born floor. -/
def retryCount : Nat :=
  ECDLP.Canonical.retryCountForBudget ecdLPInstance publishedFailureBudget

/-- This is the least positive natural count above the exact logarithmic
calibration exponent for the concrete Born failure rate. -/
lemma retryCount_is_minimal_calibration {count : Nat}
    (hone : 1 ≤ count)
    (hcalibration :
      FailureBudget.retryExponentFor
          (FiniteCyclicDLP.Concrete.Amplification.sourceFailureBudget
            canonicalProblem)
          publishedFailureBudget ≤ (count : Real)) :
    retryCount ≤ count := by
  simpa [retryCount, ECDLP.Canonical.retryCountForBudget,
    FiniteCyclicDLP.Concrete.Amplification.retryCountForBudget] using
    FailureBudget.retryCountFor_le_of_one_le_of_exponent_le
      (FiniteCyclicDLP.Concrete.Amplification.sourceFailureBudget
        canonicalProblem)
      publishedFailureBudget hone hcalibration

/-- Exact rational form of the fixed public threshold. -/
lemma publishedThreshold_eq_ninetyNineHundredths :
    FailureBudget.successThreshold publishedFailureBudget =
      ENNReal.ofReal ((99 : Real) / 100) := by
  unfold FailureBudget.successThreshold FailureBudget.value
    publishedFailureBudget
  congr 1
  norm_num

/-- The one actual circuit uses the explicit order-seven preparation and certified group oracle. -/
def algorithm (budget : FailureBudget) :=
  ECDLP.algorithm ecdLPInstance orderExpansion budget

/-- The original small-curve instance with its complete declared resource contract.

**Input.**
- The prescribed points `P = (0,1)` and `Q = (3,3)` on the certified curve
  over `F_5`, with subgroup order seven; any external reference is admitted.
**Output.**
- An optional word representing the scalar three modulo seven, alongside
  the complete retained input, quantum bank, measured cells and recovery cells.
**Resource budget.**
- The general independent scalar formulas specialize to field width three,
  Fourier width seven and binary exponents zero, one and two. The original
  logarithmic count selects complete double-reset and checked-recovery rounds.
- Resident and auxiliary limits include the one bank, all classical storage,
  complete recovery scratch and final result; depth counts the actual events.
**Success.**
- At least `1 - eta` for the supplied well-formed rational failure budget.
**Source.**
- The ECDLP reduction is [PZ03, ecc.tex:448-462]; the fixed curve and point
  equations are proved directly in this example's mathematical data module.
- Literal preparation follows [SV24, Uniform.tex:640-663].
-/
def problem (budget : FailureBudget) (wellFormed : budget.WellFormed) :=
  ECDLP.problem ecdLPInstance orderExpansion budget wellFormed

/-- Every original well-formed failure budget applies to the actual fixed example. -/
lemma mainForBudget (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    (algorithm budget).Solves (problem budget wellFormed) :=
  (ECDLP.main ecdLPInstance orderExpansion budget wellFormed).1

/-- The actual fixed example meets its original one-percent failure contract. -/
theorem main : (algorithm publishedFailureBudget).Solves
    (problem publishedFailureBudget publishedFailureBudget_wellFormed) :=
  mainForBudget publishedFailureBudget publishedFailureBudget_wellFormed

end

end Example
end EllipticCurve
end QuantumAlg

end
