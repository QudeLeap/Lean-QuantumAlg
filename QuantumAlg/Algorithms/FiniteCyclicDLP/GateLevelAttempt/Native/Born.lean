/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Observation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Born

/-!
# Original finite-cyclic terminal Born law of the literal sampler

The normalized vector and ordered exponent readout agree with the original
concrete finite-cyclic experiment. Its group, encoding and binary expansion
are unchanged. The analytical equality assigns no cost to the actual sampler.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The vector observed by the native sampler is the original concrete Born vector. -/
theorem nativeFiniteCyclic_evolved_normalized_eq (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (evolvedState P B ux).normalized =
      Concrete.BornBridge.evolvedState (circuitAccess P B ux) :=
  GateLevelAttempt.quantumCircuit_applyNormalized_eq_concrete P B ux

/-- The actual ordered terminal observation has exactly the original probability law. -/
theorem nativeFiniteCyclic_outcomePMF_eq_concrete (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    outcomePMF P B ux = Concrete.BornBridge.outcomePMF (circuitAccess P B ux) := by
  classical
  apply PMF.ext
  intro outcome
  refine (TerminalZMeasure.outcomePMF_apply (terminalMeasurement P)
    (evolvedState P B ux) outcome).trans (Eq.trans ?_
      (Concrete.BornBridge.outcomePMF_apply (circuitAccess P B ux) outcome).symm)
  apply Finset.sum_congr
  · ext basis
    rfl
  · intro basis _
    exact congrArg (fun amplitude : ℂ => ENNReal.ofReal (‖amplitude‖ ^ 2))
      (congrArg (fun state => state basis) (nativeFiniteCyclic_evolved_normalized_eq P B ux))

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native
