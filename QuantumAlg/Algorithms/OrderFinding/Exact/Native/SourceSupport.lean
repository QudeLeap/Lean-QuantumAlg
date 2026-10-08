/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Native.Born.Marginal
import all QuantumAlg.Algorithms.OrderFinding.Probability
import all QuantumAlg.Util.Classical.TerminalDecode

/-!
# Exact dyadic support of the actual native Born source

When the true order divides the phase-register cardinality, the native source
has support only on the exact periodic grid. This does not require a detached
legacy circuit construction or an assumed sampling law.
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

open scoped BigOperators

/-- A measured phase index lies on the exact order grid. -/
def ExactOutcome (r t : Nat) (outcome : TerminalZMeasure.Outcome t) : Prop :=
  ∃ s : Fin r,
    (ClassicalAlgorithms.TerminalDecode.fullRegisterIndex outcome).val =
      s.val * (2 ^ t / r)

theorem shorSourceJointAmplitude_eq_zero_of_not_dvd_period
    {t r : Nat} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (c : Fin (2 ^ t)) (k : Fin r)
    (hnot : ¬ 2 ^ t / r ∣ c.val) :
    shorSourceJointAmplitude t r (c, k) = 0 := by
  let q : Nat := 2 ^ t
  let period : Nat := q / r
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hr_le_q : r ≤ q := Nat.le_of_dvd hq_pos hrt
  have hperiod_pos : 0 < period := Nat.div_pos hr_le_q hr
  have hq_eq : r * period = q := Nat.mul_div_cancel' hrt
  have hkq : k.val < q := k.isLt.trans_le hr_le_q
  have hlength : ((q - 1 - k.val) / r) + 1 = period := by
    have hremainder : r - 1 - k.val < r := by omega
    have hdecomp :
        q - 1 - k.val = (r - 1 - k.val) + r * (period - 1) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    rw [hdecomp, Nat.add_mul_div_left _ _ hr,
      Nat.div_eq_of_lt hremainder]
    omega
  have hterm : ∀ b : Nat,
      Complex.exp (2 * Real.pi *
          (((((r : Real) * (b : Real) * (c.val : Real)) /
            (2 : Real) ^ t) : Real)) * Complex.I) =
        (ω t ^ (r * c.val)) ^ b := by
    intro b
    rw [← pow_mul, ω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hbase_ne : ω t ^ (r * c.val) ≠ 1 := by
    intro hbase
    have hbase_z : ω t ^ ((r * c.val : Nat) : Int) = 1 := by
      simpa only [zpow_natCast] using hbase
    have hdiv_z : ((q : Nat) : Int) ∣ ((r * c.val : Nat) : Int) := by
      simpa [q] using (omega_zpow_eq_one_iff t _).mp hbase_z
    have hdiv : q ∣ r * c.val := by
      exact_mod_cast hdiv_z
    rcases hdiv with ⟨multiple, hmultiple⟩
    apply hnot
    refine ⟨multiple, ?_⟩
    have hcancel : r * c.val = r * (period * multiple) := by
      calc
        r * c.val = q * multiple := hmultiple
        _ = (r * period) * multiple := by rw [hq_eq]
        _ = r * (period * multiple) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hr hcancel
  have hbase_pow : (ω t ^ (r * c.val)) ^ period = 1 := by
    calc
      (ω t ^ (r * c.val)) ^ period =
          ω t ^ ((r * c.val) * period) :=
        (pow_mul (ω t) (r * c.val) period).symm
      _ = ω t ^ (q * c.val) := by
        congr 1
        calc
          (r * c.val) * period = (r * period) * c.val := by ac_rfl
          _ = q * c.val := by rw [hq_eq]
      _ = (ω t ^ q) ^ c.val :=
        pow_mul (ω t) q c.val
      _ = 1 := by simp [q, omega_pow_eq_one]
  rw [shorSourceJointAmplitude_eq_orbit_phase_mul_quotient_step_sum hr]
  rw [shorSourceJointQuotientIndices_eq_range hr hkq]
  change _ * (_ * (Finset.range (((q - 1 - k.val) / r) + 1)).sum _) = _
  rw [hlength]
  simp_rw [hterm]
  rw [geom_sum_eq hbase_ne, hbase_pow]
  simp

theorem orderFindingPublicOutcomeProbability_eq_zero_of_not_dvd_period
    {t r : Nat} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (c : Fin (2 ^ t)) (k : Fin r)
    (hnot : ¬ 2 ^ t / r ∣ c.val) :
    orderFindingPublicOutcomeProbability t r (c, k) = 0 := by
  unfold orderFindingPublicOutcomeProbability shorSourceJointProbability
  rw [shorSourceJointAmplitude_eq_zero_of_not_dvd_period hr hrt c k hnot]
  simp

/-- The production circuit has probability one on the exact dyadic support
whenever the true order divides the phase-register cardinality. -/
theorem exactMeasurementModel {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (hrt : r ∣ 2 ^ t) :
    (sourceOutcomePMF A).toOuterMeasure
      {outcome | ExactOutcome r t outcome} = 1 := by
    classical
    let q : Nat := 2 ^ t
    let period : Nat := q / r
    have hq_pos : 0 < q := by
      dsimp [q]
      positivity
    have hr_le_q : r ≤ q := Nat.le_of_dvd hq_pos hrt
    have hperiod_pos : 0 < period :=
      Nat.div_pos hr_le_q hinput.order_pos
    have hq_eq : r * period = q := Nat.mul_div_cancel' hrt
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro outcome houtcome
    obtain ⟨c, rfl⟩ :=
      (phaseOutcome_bijective t).2 outcome
    have hdvd : period ∣ c.val := by
      by_contra hnot
      have hnot' : ¬ 2 ^ t / r ∣ c.val := by
        simpa [period, q] using hnot
      have hzero_each (k : Fin r) :
          orderFindingPublicOutcomeProbability t r (c, k) = 0 :=
        orderFindingPublicOutcomeProbability_eq_zero_of_not_dvd_period
          hinput.order_pos hrt c k hnot'
      have hzero :
          (sourceOutcomePMF A)
              (phaseOutcome t c) = 0 := by
        rw [sourceOutcomePMF_eq_sourceMarginal hinput A]
        simp [hzero_each]
      exact ((PMF.mem_support_iff _ _).mp houtcome) hzero
    change ∃ s : Fin r,
      (ClassicalAlgorithms.TerminalDecode.fullRegisterIndex (phaseOutcome t c)).val =
        s.val * (2 ^ t / r)
    rw [fullRegisterIndex_phaseOutcome]
    have hc_lt : c.val < r * period := by
      rw [hq_eq]
      exact c.isLt
    let s : Fin r :=
      ⟨c.val / period,
        (Nat.div_lt_iff_lt_mul hperiod_pos).2 hc_lt⟩
    refine ⟨s, ?_⟩
    change c.val = (c.val / period) * (2 ^ t / r)
    simpa [q, period] using (Nat.div_mul_cancel hdvd).symm

end

end QuantumAlg.OrderFinding.Native
