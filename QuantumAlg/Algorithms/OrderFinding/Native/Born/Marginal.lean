/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Native.Born.Orbit
import all QuantumAlg.Algorithms.OrderFinding.Native.Born.MeasurementFiber
import all QuantumAlg.Algorithms.OrderFinding.Native.Born.Distribution
import all QuantumAlg.Core.Measure.Distribution

/-!
# Native source Born marginal over the exact modular orbit

The measured phase probability sums the squared amplitudes of all target
basis states. Only the true modular orbit contributes, and its mass equals
the independent source-joint probability marginal.
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

open scoped BigOperators

/-- The actual terminal Born probability is the target-register marginal of
the source joint distribution. -/
theorem sourceOutcomePMF_eq_sourceMarginal {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (c : Fin (2 ^ t)) :
    (sourceOutcomePMF A) (phaseOutcome t c) =
      ENNReal.ofReal
        (∑ k : Fin r, orderFindingPublicOutcomeProbability t r (c, k)) := by
  classical
  unfold sourceOutcomePMF
  rw [TerminalZMeasure.outcomePMF_apply, sourceMeasurement_fiber,
    Finset.sum_map]
  simp_rw [sourceFiberEmbedding_apply, evolvedState_amplitude]
  change (∑ y : Fin (2 ^ m),
      ENNReal.ofReal (‖sourceAmplitude A c y‖ ^ 2)) = _
  calc
    (∑ y : Fin (2 ^ m),
        ENNReal.ofReal (‖sourceAmplitude A c y‖ ^ 2)) =
        ∑ y ∈ (Finset.univ : Finset (Fin r)).map
            (orbitTargetEmbedding hinput A),
          ENNReal.ofReal (‖sourceAmplitude A c y‖ ^ 2) := by
      symm
      apply Finset.sum_subset (by simp)
      intro y _hy hnot
      have hnotImage :
          y ∉ (Finset.univ : Finset (Fin r)).image (orbitTarget A) := by
        simpa only [mem_orbitTargetEmbedding_map_iff hinput A y] using hnot
      rw [sourceAmplitude_eq_zero_of_not_mem_orbit
        hinput A c y hnotImage]
      simp
    _ = ∑ k : Fin r,
        ENNReal.ofReal
          (‖sourceAmplitude A c (orbitTarget A k)‖ ^ 2) := by
      rw [Finset.sum_map]
      simp
    _ = ∑ k : Fin r,
        ENNReal.ofReal (orderFindingPublicOutcomeProbability t r (c, k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sourceAmplitude_orbitTarget_eq_star hinput A]
      simp [orderFindingPublicOutcomeProbability, shorSourceJointProbability]
    _ = ENNReal.ofReal
        (∑ k : Fin r, orderFindingPublicOutcomeProbability t r (c, k)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      intro k _hk
      exact orderFindingPublicOutcomeProbability_nonneg t r (c, k)


end

end QuantumAlg.OrderFinding.Native
