/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Observation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Attempt.Born

/-!
# The actual literal sampler and the original finite-cyclic Born experiment

The original literal preparation produces the same normalized vector as
the analytical preparation, followed by the same opaque group action and
two inverse Fourier transforms. Both terminal measurements read the same
leading exponent bits. Their Born laws therefore agree exactly, including
the single-term order expansion. This equality transfers no resource cost
from the analytical preparation to the actual literal circuit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The normalized vector observed by the actual sampler is the original concrete Born vector. -/
theorem nativeECDLP_evolved_normalized_eq
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) :
    (evolvedState I B A).normalized =
      FiniteCyclicDLP.Concrete.BornBridge.evolvedState (circuitAccess I A) :=
  GateLevelAttempt.quantumCircuit_applyNormalized_eq_analytical I B A

/-- Literal native sampling has exactly the original finite-cyclic terminal probability law. -/
theorem nativeECDLP_outcomePMF_eq_concrete
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) :
    outcomePMF I B A =
      FiniteCyclicDLP.Concrete.BornBridge.outcomePMF (circuitAccess I A) := by
  classical
  apply PMF.ext
  intro outcome
  refine (TerminalZMeasure.outcomePMF_apply (terminalMeasurement I)
    (evolvedState I B A) outcome).trans (Eq.trans ?_
      (FiniteCyclicDLP.Concrete.BornBridge.outcomePMF_apply (circuitAccess I A) outcome).symm)
  apply Finset.sum_congr
  · ext basis
    rfl
  · intro basis _
    exact congrArg (fun amplitude : ℂ => ENNReal.ofReal (‖amplitude‖ ^ 2))
      (congrArg (fun state => state basis) (nativeECDLP_evolved_normalized_eq I B A))

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
