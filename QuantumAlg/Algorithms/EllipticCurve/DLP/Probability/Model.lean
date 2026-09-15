/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
public import QuantumAlg.Algorithms.Factoring.Common
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Amplification.Model

/-!
# Original ECDLP probability witness and retry count

The chosen secret is a mathematical witness for the useful Fourier event.
The original public failure budget fixes the finite repetition count.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Probability-side input carrying the actual elliptic-curve secret. -/
def input (I : ECDLPInstance E) : FiniteCyclicDLP.Input (problem I) where
  secret := secret I
  target_eq_generator_pow := secret_spec I

/-- Independent-attempt count calibrated to the public failure budget. -/
public def retryCountForBudget (I : ECDLPInstance E)
    (budget : Factoring.FailureBudget) : Nat :=
  FiniteCyclicDLP.Concrete.Amplification.retryCountForBudget
    (problem I) budget

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
