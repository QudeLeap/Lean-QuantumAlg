/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Util.Real.ReciprocalSquareTail
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# QPE nearest-point and high-confidence Born windows

The source geometric amplitudes give both the 4/pi^2 nearest-point bound and
an explicit tail bound outside a periodic phase window. Finite good and bad
events partition the normalized Born distribution, so the scalar tail bound
implies confidence at least 1-eta [Lin22, phaseestimation.tex:647-715].

These statements concern the exact vector of the executable QPE unitary.
They do not construct a run or accept an independently chosen outcome PMF.
Native endpoint proofs separately identify their actual stored result with
this same mathematical readout.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open scoped BigOperators


/-- The success event says that the measured bit vector encodes a dyadic phase
estimate within the advertised periodic error. -/
def SuccessfulOutcome {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (outcome : TerminalZMeasure.Outcome t) : Prop :=
  ∃ j : Fin (2 ^ t), outcome = qpeOutcome t j ∧
    qpePhaseDistance t P.phase j ≤ 1 / (2 : Real) ^ t

/-- Terminal outcomes whose canonical decoded phase lies strictly inside a
periodic window of radius `rho`. -/
def WithinPhaseWindow {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (ρ : Real)
    (outcome : TerminalZMeasure.Outcome t) : Prop :=
  qpePhaseDistance t P.phase
    (TerminalZMeasure.fullRegisterIndex outcome) < ρ

/-- Complementary terminal event at or outside the periodic phase window. -/
def OutsidePhaseWindow {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (ρ : Real)
    (outcome : TerminalZMeasure.Outcome t) : Prop :=
  ρ <= qpePhaseDistance t P.phase
    (TerminalZMeasure.fullRegisterIndex outcome)

lemma nearestIndex_successful {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) :
    SuccessfulOutcome P t (qpeOutcome t (qpeNearestIndex t P.phase)) := by
  refine ⟨qpeNearestIndex t P.phase, rfl, ?_⟩
  calc
    qpePhaseDistance t P.phase (qpeNearestIndex t P.phase) ≤
        1 / (2 * (2 : Real) ^ t) := qpeNearestIndex_distance_le t P.phase
    _ ≤ 1 / (2 : Real) ^ t := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * (2 : Real) ^ t)
        (by positivity : 0 < (2 : Real) ^ t)]
      nlinarith [show 0 < (2 : Real) ^ t by positivity]

/-- The Born event of the exact QPE vector attains the source lower bound. -/
lemma born_successProbability_ge {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) :
    ENNReal.ofReal (4 / Real.pi ^ 2) ≤
      ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).toOuterMeasure
        {outcome | SuccessfulOutcome P t outcome} := by
  let nearest := qpeOutcome t (qpeNearestIndex t P.phase)
  calc
    ENNReal.ofReal (4 / Real.pi ^ 2) ≤
        (qpeMeasurement t n).outcomePMF (qpeEvolvedState P t) nearest :=
      qpeNearestOutcome_probability_ge P t
    _ = ((qpeMeasurement t n).outcomePMF
          (qpeEvolvedState P t)).toOuterMeasure {nearest} := by
      rw [PMF.toOuterMeasure_apply_singleton]
    _ ≤ ((qpeMeasurement t n).outcomePMF
          (qpeEvolvedState P t)).toOuterMeasure
          {outcome | SuccessfulOutcome P t outcome} := by
      apply ((qpeMeasurement t n).outcomePMF
        (qpeEvolvedState P t)).toOuterMeasure.mono
      intro outcome member
      rw [Set.mem_singleton_iff] at member
      subst outcome
      exact nearestIndex_successful P t

private lemma qpeOutcome_bijective (t : Nat) :
    Function.Bijective (qpeOutcome t) := by
  apply (Fintype.bijective_iff_injective_and_card (qpeOutcome t)).2
  exact ⟨qpeOutcome_injective t, by simp⟩

/-- The exact Born bad-window mass is the finite geometric-amplitude tail. -/
lemma born_badWindowProbability_eq_badIndexMass {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) (ρ : Real) :
    ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).toOuterMeasure
        {outcome | OutsidePhaseWindow P t ρ outcome} =
      ENNReal.ofReal (qpeBadIndexMass t P.phase ρ) := by
  classical
  let equivalence : Fin (2 ^ t) ≃ TerminalZMeasure.Outcome t :=
    Equiv.ofBijective (qpeOutcome t) (qpeOutcome_bijective t)
  rw [PMF.toOuterMeasure_apply_fintype, ← Equiv.sum_comp equivalence]
  rw [qpeBadIndexMass,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [equivalence, Equiv.ofBijective_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, OutsidePhaseWindow, qpeOutcome_fullRegisterIndex,
    qpeMeasurement_outcomePMF_apply, Finset.sum_filter]

/-- Source high-confidence failure bound for the exact QPE Born distribution. -/
lemma born_badWindowProbability_le {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat)
    (ρ : Real) (hrho : 0 < ρ) :
    ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).toOuterMeasure
        {outcome | OutsidePhaseWindow P t ρ outcome} ≤
      ENNReal.ofReal
        (1 / (2 * (2 : Real) ^ t * ρ) +
          1 / (2 * ((2 : Real) ^ t * ρ) ^ 2)) := by
  rw [born_badWindowProbability_eq_badIndexMass P t ρ]
  exact ENNReal.ofReal_le_ofReal (qpeBadIndexMass_le t P.phase ρ hrho)

/-- Good and bad windows partition the exact QPE Born distribution. -/
lemma born_window_add_bad_eq_one {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) (ρ : Real) :
    ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).toOuterMeasure
        {outcome | WithinPhaseWindow P t ρ outcome} +
      ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).toOuterMeasure
        {outcome | OutsidePhaseWindow P t ρ outcome} =
      (1 : ENNReal) := by
  let output := (qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
    ← Finset.sum_add_distrib]
  calc
    Finset.univ.sum (fun value =>
        Set.indicator
            {outcome | WithinPhaseWindow P t ρ outcome}
            output value +
          Set.indicator
            {outcome | OutsidePhaseWindow P t ρ outcome}
            output value) = Finset.univ.sum output := by
      apply Finset.sum_congr rfl
      intro value _member
      by_cases good : WithinPhaseWindow P t ρ value
      · have notBad : ¬ OutsidePhaseWindow P t ρ value := by
          simpa [WithinPhaseWindow, OutsidePhaseWindow, not_le] using good
        simp [good, notBad]
      · have bad : OutsidePhaseWindow P t ρ value := by
          simpa [WithinPhaseWindow, OutsidePhaseWindow, not_lt] using good
        simp [good, bad]
    _ = 1 := by simpa only [tsum_fintype] using output.tsum_coe

private lemma qpeWindowFailureBound_le_eta
    (t : Nat) (ρ η : Real) (hrho : 0 < ρ)
    (heta : 0 < η) (heta_le : η ≤ 1)
    (hscale : η⁻¹ ≤ (2 : Real) ^ t * ρ) :
    1 / (2 * (2 : Real) ^ t * ρ) +
        1 / (2 * ((2 : Real) ^ t * ρ) ^ 2) ≤ η := by
  let x : Real := (2 : Real) ^ t * ρ
  have hx : 0 < x := by dsimp [x]; positivity
  have inverseLe : 1 / x ≤ η := by
    calc
      1 / x ≤ 1 / η⁻¹ :=
        one_div_le_one_div_of_le (inv_pos.mpr heta) (by simpa [x] using hscale)
      _ = η := by field_simp [heta.ne']
  have inverseNonnegative : 0 ≤ 1 / x := one_div_nonneg.mpr hx.le
  have squareLe : (1 / x) ^ 2 ≤ η ^ 2 :=
    pow_le_pow_left₀ inverseNonnegative inverseLe 2
  have etaSquareLe : η ^ 2 ≤ η := by
    nlinarith [sq_nonneg (η - 1)]
  have rewriteBound :
      1 / (2 * (2 : Real) ^ t * ρ) +
          1 / (2 * ((2 : Real) ^ t * ρ) ^ 2) =
        (1 / x + (1 / x) ^ 2) / 2 := by
    dsimp [x]
    field_simp [pow_ne_zero t (by norm_num : (2 : Real) ≠ 0), hrho.ne']
  rw [rewriteBound]
  nlinarith

/-- The mathematical QPE Born window succeeds with the source confidence bound. -/
lemma born_successProbability_ge_one_sub_eta {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat)
    (ρ η : Real) (hrho : 0 < ρ) (heta : 0 < η)
    (heta_le : η ≤ 1) (hscale : η⁻¹ ≤ (2 : Real) ^ t * ρ) :
    ENNReal.ofReal (1 - η) ≤
      ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).toOuterMeasure
        {outcome | WithinPhaseWindow P t ρ outcome} := by
  have bad := born_badWindowProbability_le P t ρ hrho
  have scalar := qpeWindowFailureBound_le_eta t ρ η hrho heta heta_le hscale
  have badEta :
      ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).toOuterMeasure
        {outcome | OutsidePhaseWindow P t ρ outcome} ≤
        ENNReal.ofReal η :=
    bad.trans (ENNReal.ofReal_le_ofReal scalar)
  have partition := born_window_add_bad_eq_one P t ρ
  have goodEq :
      ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).toOuterMeasure
        {outcome | WithinPhaseWindow P t ρ outcome} =
        (1 : ENNReal) -
          ((qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)).toOuterMeasure
        {outcome | OutsidePhaseWindow P t ρ outcome} :=
    ENNReal.eq_sub_of_add_eq' (by norm_num) partition
  rw [ENNReal.ofReal_sub 1 heta.le, ENNReal.ofReal_one, goodEq]
  exact tsub_le_tsub_left badEta (1 : ENNReal)

end

end QuantumAlg.QuantumPhaseEstimation
