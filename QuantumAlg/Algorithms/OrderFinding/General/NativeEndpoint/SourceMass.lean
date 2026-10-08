/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Native.Born.Marginal
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.SourceEvent
import all QuantumAlg.Algorithms.OrderFinding.Probability

/-!
# Recoverable-event mass of the actual native Born source

The actual native source word's terminal Born mass on recoverable phase
outcomes equals the independent analytic source-joint success mass.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

open scoped BigOperators

private theorem sourceEvent_coord_irrel {G : Type*} [Monoid G]
    {t r : Nat} (g : G) (phase : Fin (2 ^ t)) (left right : Fin r) :
    orderFindingOutputSuccessEvent g (phase, left) ↔
      orderFindingOutputSuccessEvent g (phase, right) := by
  rfl

/-- The production circuit's successful Born mass equals the source-joint
successful mass used by the typed general endpoint. -/
theorem nativeRecoverableMass_eq_sourceSuccessMass {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) :
    (OrderFinding.Native.sourceOutcomePMF A).toOuterMeasure
        {outcome |
          NativeRecoverableOutcome
            (ZMod.unitOfCoprime x hinput.coprime) r outcome} =
      ENNReal.ofReal
        (orderFindingOutputSuccessMass
          (ZMod.unitOfCoprime x hinput.coprime)
          (orderFindingPublicOutcomeProbability t r)) := by
  classical
  let e : Fin (2 ^ t) ≃ TerminalZMeasure.Outcome t :=
    Equiv.ofBijective (OrderFinding.Native.phaseOutcome t)
      (OrderFinding.Native.phaseOutcome_bijective t)
  rw [PMF.toOuterMeasure_apply_fintype, ← Equiv.sum_comp e]
  simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, NativeRecoverableOutcome,
    OrderFinding.Native.fullRegisterIndex_phaseOutcome]
  simp_rw [OrderFinding.Native.sourceOutcomePMF_eq_sourceMarginal hinput A]
  rw [orderFindingOutputSuccessMass, Fintype.sum_prod_type,
    ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro c _hc
    by_cases hsuccess : ∃ k : Fin r,
        orderFindingOutputSuccessEvent
          (ZMod.unitOfCoprime x hinput.coprime) (c, k)
    · rw [if_pos hsuccess]
      obtain ⟨witness, hwitness⟩ := hsuccess
      have hall : ∀ k : Fin r,
          orderFindingOutputSuccessEvent
            (ZMod.unitOfCoprime x hinput.coprime) (c, k) := by
        intro k
        exact (sourceEvent_coord_irrel
          (ZMod.unitOfCoprime x hinput.coprime) c k witness).mpr hwitness
      simp_rw [if_pos (hall _)]
    · rw [if_neg hsuccess]
      have hnone : ∀ k : Fin r,
          ¬ orderFindingOutputSuccessEvent
            (ZMod.unitOfCoprime x hinput.coprime) (c, k) := by
        intro k hk
        exact hsuccess ⟨k, hk⟩
      simp_rw [if_neg (hnone _)]
      simp
  · intro c _hc
    exact Finset.sum_nonneg fun k _hk => by
      by_cases hsuccess : orderFindingOutputSuccessEvent
          (ZMod.unitOfCoprime x hinput.coprime) (c, k)
      · rw [if_pos hsuccess]
        exact orderFindingPublicOutcomeProbability_nonneg t r (c, k)
      · simp [hsuccess]


end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
