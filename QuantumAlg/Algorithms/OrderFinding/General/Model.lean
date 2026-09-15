/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.BornModel
import all QuantumAlg.Algorithms.OrderFinding.Eigenstructure
import all QuantumAlg.Algorithms.OrderFinding.Probability
import all QuantumAlg.Util.Order.Finding
import all QuantumAlg.Util.RationalApproximation
import Mathlib.Data.Nat.Totient

/-!
# Original general order-finding success mathematics

The source-joint recovery bound, finite small-modulus cases and actual query
Born marginal keep their original statements. They do not depend on a
runtime implementation, terminal ownership, or a classical recovery executor.
-/

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

namespace OrderFinding

/-! ## Source probability and recovery, without resource metadata -/

/-- Every source-certified recoverable joint event decodes to denominator `r`,
and the source success lower bound is carried by exactly those events. -/
theorem sourceJoint_recoverableEventSuccess {t r : Nat}
    (hr : 0 < r) (cert : ShorSourceJointEventMapCertificate t r) :
    (∀ outcome,
      outcome ∈ shorSourceJointRecoverableEvents (t := t) (r := r) cert.eventOf →
        ∃ d, d ∈ shorRecoverableFractionIndices r ∧
          ∃ n,
            (d.val : Rat) / (r : Rat) =
              (((outcome.1.val : Real) / (2 : Real) ^ t).convergent n) ∧
            ((((outcome.1.val : Real) / (2 : Real) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        (shorSourceJointRecoverableEvents
          (t := t) (r := r) cert.eventOf).sum cert.prob := by
  constructor
  · intro outcome houtcome
    rcases Finset.mem_image.mp houtcome with ⟨idx, hidx, houtcome_eq⟩
    rcases idx with ⟨k, d⟩
    have hd : d ∈ shorRecoverableFractionIndices r := by
      simpa [shorRecoverableStateIndices] using hidx
    cases houtcome_eq
    refine ⟨d, hd, ?_⟩
    have hcop : Nat.Coprime d.val r := by
      have hd' : r.Coprime d.val := by
        simpa [shorRecoverableFractionIndices] using hd
      simpa [Nat.coprime_comm] using hd'
    exact goodPhaseRegisterOutcome_denominatorRecovery hr hcop (cert.good d hd)
  · exact cert.successLowerBound_le_recoverableMass hr

open ShorSourceJointEventMapCertificate in
/-- Concrete rounded-nearest-fraction specialization of the source theorem. -/
theorem sourceJoint_scaledErrorRecoverableEventSuccess {t r : Nat}
    (hr : 0 < r) (hq : (r : Real) ^ 2 < (2 : Real) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t) :
    (∀ outcome,
      outcome ∈ shorSourceJointRecoverableEvents
          (t := t) (r := r) (shorNearestFractionEvent hr hq) →
        ∃ d, d ∈ shorRecoverableFractionIndices r ∧
          ∃ n,
            (d.val : Rat) / (r : Rat) =
              (((outcome.1.val : Real) / (2 : Real) ^ t).convergent n) ∧
            ((((outcome.1.val : Real) / (2 : Real) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        (shorSourceJointRecoverableEvents
          (t := t) (r := r) (shorNearestFractionEvent hr hq)).sum
            (shorSourceJointProbability t r) := by
  let cert :=
    ofSourceJointProbabilityRoundedNearestFractionEventsOfScaledError hr hq hlarge
  simpa [cert,
    ofSourceJointProbabilityRoundedNearestFractionEventsOfScaledError,
    ofSourceJointProbabilityRoundedNearestFractionEvents,
    ofSourceJointProbabilityInferInjectivity,
    ofSourceJointProbability] using
      sourceJoint_recoverableEventSuccess hr cert

open ShorSourceJointEventMapCertificate in
/-- The source recovery theorem over the public register window
`N^2 <= 2^t < 2N^2`, including the finite small-modulus residual cases. -/
theorem sourceJoint_publicRegisterRecoverableEventSuccess
    {N x t r : Nat}
    (hinput : OrderFinding.Input N x r)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2) :
    let hq : (r : Real) ^ 2 < (2 : Real) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister
    (∀ outcome,
      outcome ∈ shorSourceJointRecoverableEvents
          (t := t) (r := r) (shorNearestFractionEvent hinput.order_pos hq) →
        ∃ d, d ∈ shorRecoverableFractionIndices r ∧
          ∃ n,
            (d.val : Rat) / (r : Rat) =
              (((outcome.1.val : Real) / (2 : Real) ^ t).convergent n) ∧
            ((((outcome.1.val : Real) / (2 : Real) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        (shorSourceJointRecoverableEvents
          (t := t) (r := r) (shorNearestFractionEvent hinput.order_pos hq)).sum
            (shorSourceJointProbability t r) := by
  by_cases hN : 12 ≤ N
  · have hq : (r : Real) ^ 2 < (2 : Real) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister
    have hlarge : 12 * r ≤ 2 ^ t :=
      largeRegister_of_publicRegisterBound_of_modulus_ge_twelve
        hN (input_order_lt_modulus hinput) hregister
    simpa [hq] using
      sourceJoint_scaledErrorRecoverableEventSuccess hinput.order_pos hq hlarge
  · have hNlt : N < 12 := Nat.lt_of_not_ge hN
    have hq : (r : Real) ^ 2 < (2 : Real) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister
    rcases smallModulus_publicRegisterWindow_large_or_possibleResidual
        hinput hNlt hregister hupper with hlarge | hres
    · simpa [hq] using
        sourceJoint_scaledErrorRecoverableEventSuccess hinput.order_pos hq hlarge
    · have hbounds :
          ∀ idx, idx ∈ shorRecoverableStateIndices r →
            (11 / 12 : Real) ≤
                (((((2 ^ t - 1 - idx.1.val) / r) + 1 : Nat) : Real) *
                    (r : Real)) /
                  (2 : Real) ^ t ∧
              (((((2 ^ t - 1 - idx.1.val) / r) + 1 : Nat) : Real) *
                    (r : Real)) /
                  (2 : Real) ^ t ≤ (13 / 12 : Real) := by
        intro idx _hidx
        rcases idx with ⟨k, _d⟩
        rcases hres with h2 | hres
        · rcases h2 with ⟨hN2, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k
          norm_num
        rcases hres with h3 | hres
        · rcases h3 with ⟨hN3, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k <;> norm_num
        rcases hres with h4 | hres
        · rcases h4 with ⟨hN4, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k <;> norm_num
        rcases hres with h5 | h7
        · rcases h5 with ⟨hN5, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k <;> norm_num
        · rcases h7 with ⟨hN7, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k <;> norm_num
      let cert : ShorSourceJointEventMapCertificate t r :=
        ofSourceJointProbabilityRoundedNearestFractionEventsOfQuotientBounds
          hinput.order_pos hq hbounds
      simpa [hq, cert,
        ofSourceJointProbabilityRoundedNearestFractionEventsOfQuotientBounds,
        ofSourceJointProbabilityRoundedNearestFractionEvents,
        ofSourceJointProbabilityInferInjectivity,
        ofSourceJointProbability] using
          sourceJoint_recoverableEventSuccess hinput.order_pos cert

/-- Source-level public output-success bound, before embedding into the actual
implementationAlgorithm Born PMF. -/
theorem sourceOutputSuccessLowerBound {N x t r : Nat}
    (hinput : OrderFinding.Input N x r)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2) :
    orderFindingOutputSuccessLowerBound r ≤
      orderFindingOutputSuccessMass
        (ZMod.unitOfCoprime x hinput.coprime)
        (orderFindingPublicOutcomeProbability t r) := by
  have hsupport :=
    sourceJoint_publicRegisterRecoverableEventSuccess hinput hregister hupper
  have hq : (r : Real) ^ 2 < (2 : Real) ^ t :=
    publicRegisterBound_implies_scaledError_of_order_lt_modulus
      (input_order_lt_modulus hinput) hregister
  rcases hsupport with ⟨hcf, hmass⟩
  refine
    shorOrderRecoverySuccessLowerBound_le_outputSuccessMass_of_recoverableEvents
      (eventOf := shorNearestFractionEvent hinput.order_pos hq)
      (prob := orderFindingPublicOutcomeProbability t r) ?_ hinput.order_pos
      (orderOf_zmodUnitOfCoprime_eq_input_order hinput) hmass ?_
  · intro outcome houtcome
    rcases hcf outcome houtcome with ⟨_d, _hd, n, _hfrac, hden⟩
    exact ⟨n, hden⟩
  · intro outcome
    exact orderFindingPublicOutcomeProbability_nonneg t r outcome

/-- Source-level output-success bound under the scaled-error and large-register
hypotheses. Unlike the public-window wrapper, this theorem requires no upper
bound of the form `2^t < 2*N^2`. -/
theorem sourceOutputSuccessLowerBound_of_scaledError {N x t r : Nat}
    (hinput : OrderFinding.Input N x r)
    (hq : (r : Real) ^ 2 < (2 : Real) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t) :
    orderFindingOutputSuccessLowerBound r ≤
      orderFindingOutputSuccessMass
        (ZMod.unitOfCoprime x hinput.coprime)
        (orderFindingPublicOutcomeProbability t r) := by
  have hsupport :=
    sourceJoint_scaledErrorRecoverableEventSuccess
      hinput.order_pos hq hlarge
  rcases hsupport with ⟨hcf, hmass⟩
  refine
    shorOrderRecoverySuccessLowerBound_le_outputSuccessMass_of_recoverableEvents
      (eventOf := shorNearestFractionEvent hinput.order_pos hq)
      (prob := orderFindingPublicOutcomeProbability t r) ?_ hinput.order_pos
      (orderOf_zmodUnitOfCoprime_eq_input_order hinput) hmass ?_
  · intro outcome houtcome
    rcases hcf outcome houtcome with ⟨_d, _hd, n, _hfrac, hden⟩
    exact ⟨n, hden⟩
  · intro outcome
    exact orderFindingPublicOutcomeProbability_nonneg t r outcome

namespace ShorSourceJoint

/-- A raw phase-register output is recoverable when some source orbit
coordinate certifies the true order as a continued-fraction denominator. -/
def RecoverableOutcome {G : Type*} [Monoid G] {t : Nat}
    (g : G) (r : Nat) (outcome : Outcome t) : Prop :=
  ∃ k : Fin r, orderFindingOutputSuccessEvent g (decodeOutcome outcome, k)

end ShorSourceJoint

namespace BornBridge

theorem orderFindingOutputSuccessEvent_prod_iff
    {G : Type*} [Monoid G] {t r : Nat} (g : G)
    (c : Fin (2 ^ t)) (left right : Fin r) :
    orderFindingOutputSuccessEvent g (c, left) ↔
      orderFindingOutputSuccessEvent g (c, right) := by
  rfl

/-- The production circuit's successful Born mass equals the source-joint
successful mass used by the typed general endpoint. -/
theorem bornSuccessMass_eq_sourceOutputSuccessMass {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) :
    ((measurement t m).outcomePMF (evolvedState A)).toOuterMeasure
        {outcome |
          ShorSourceJoint.RecoverableOutcome
            (ZMod.unitOfCoprime x hinput.coprime) r outcome} =
      ENNReal.ofReal
        (orderFindingOutputSuccessMass
          (ZMod.unitOfCoprime x hinput.coprime)
          (orderFindingPublicOutcomeProbability t r)) := by
  classical
  let e : Fin (2 ^ t) ≃ Outcome t :=
    Equiv.ofBijective (measurementOutcome t)
      (orderFindingMeasurementOutcome_bijective t)
  rw [PMF.toOuterMeasure_apply_fintype, ← Equiv.sum_comp e]
  simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, ShorSourceJoint.RecoverableOutcome,
    decodeOutcome_measurementOutcome]
  simp_rw [bornOutcomeProbability_eq_sourceMarginal hinput A]
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
        exact (orderFindingOutputSuccessEvent_prod_iff
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

/-- Same production-measurement law, written at the public circuit input. -/
theorem sourceMeasurementModel {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) :
    ((measurement t m).outcomePMF
        (evolvedState A)).toOuterMeasure
        {outcome |
          ShorSourceJoint.RecoverableOutcome
            (ZMod.unitOfCoprime x hinput.coprime) r outcome} =
      ENNReal.ofReal
        (orderFindingOutputSuccessMass
          (ZMod.unitOfCoprime x hinput.coprime)
          (orderFindingPublicOutcomeProbability t r)) :=
  bornSuccessMass_eq_sourceOutputSuccessMass hinput A

end BornBridge

end OrderFinding

end

end QuantumAlg
