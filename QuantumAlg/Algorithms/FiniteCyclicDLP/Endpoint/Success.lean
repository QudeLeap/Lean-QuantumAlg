/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Distribution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Candidate.Selection
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Success.Amplification

/-!
# Original two-thirds success of the actual finite-cyclic endpoint

The original selected Fourier family has its original positive totient floor.
The actual joint sample law and original conservative retry count amplify
that floor. On this event the actual complete classical selector writes the
original secret; neither independent sampling nor recovery success is assumed.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open Execution
open GateLevelAttempt.Native (sampleWidth)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

/-- The original conservative retry count gives the original exact answer with probability 2/3. -/
theorem finiteCyclic_outputLaw_success (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      outputLaw P B A (.optionSome (CShape.wordOfNat (orderWidth P) secret.secret.val)) := by
  rw [← PMF.toOuterMeasure_apply_singleton, outputLaw, sampledJointLaw,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  refine (finiteCyclic_selected_vector_probability P B A secret).trans
    (MeasureTheory.measure_mono (fun outcomes selected => ?_))
  exact nativeRecovery_selected_samples P B A secret (retryCount P) outcomes selected

/-- The trace distribution of the one actual complete run meets the original success threshold. -/
theorem finiteCyclic_run_success (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (secret : Probability.SecretInput P)
    {Reference : Register} (input : Execution.Input (pre P) Reference)
    (originalTarget : ∀ store, 0 < (input.state.block store).mass →
      store.read (targetRef P) = targetValue A) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (run P B A).outputDistribution input
        (.optionSome (CShape.wordOfNat (orderWidth P) secret.secret.val)) := by
  rw [finiteCyclic_run_outputDistribution P B A input originalTarget]
  exact finiteCyclic_outputLaw_success P B A secret

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
