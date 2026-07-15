/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.QPE
public import QuantumAlg.Util.OrderCandidate
public import QuantumAlg.Util.RationalApproximation
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic

/-!
# Order-finding probability and source-success bridge

This module isolates the general-order phase-register distribution,
continued-fraction goodness predicate, and Shor-style source-event success
certificates used by order finding. The analytic geometric-sum lower bound is
kept behind explicit certificate fields until it is formalized from source.

The distribution shape and continued-fraction recovery target are the
non-dyadic period-finding analysis from Shor's algorithm [Sho95,
source.tex:1614-1633] [dW19, qcnotes.tex:2279-2301].
-/

@[expose] public section

namespace QuantumAlg
namespace OrderFinding

noncomputable section

/-- General-order eigenphase used by the phase-register sampling distribution. -/
def generalOrderEigenphase (s r : ℕ) : ℝ :=
  (s : ℝ) / r

@[simp]
theorem generalOrderEigenphase_eq (s r : ℕ) :
    generalOrderEigenphase s r = (s : ℝ) / r :=
  rfl

/-- Phase-register output state for a general order, after inverse QFT. This
definition intentionally separates the sampling distribution from later
lower-bound estimates. -/
def generalOrderPhaseRegisterState (t s r : ℕ) : PureState (Qubits t) :=
  (invQFT t).apply (phasePureState t (generalOrderEigenphase s r))

/-- Born-rule sampling distribution over the phase-register outcomes for a
general-order eigenphase `s/r`. -/
def generalOrderPhaseRegisterDistribution (t s r : ℕ) (j : Fin (2 ^ t)) : ℝ :=
  PureState.probOutcome (generalOrderPhaseRegisterState t s r) j

theorem generalOrderPhaseRegisterDistribution_nonneg (t s r : ℕ)
    (j : Fin (2 ^ t)) :
    0 ≤ generalOrderPhaseRegisterDistribution t s r j :=
  PureState.probOutcome_nonneg _ _

private theorem sum_generalOrderPhaseRegisterDistribution (t s r : ℕ) :
    ∑ j : Fin (2 ^ t), generalOrderPhaseRegisterDistribution t s r j = 1 := by
  simpa [generalOrderPhaseRegisterDistribution] using
    PureState.sum_probOutcome (generalOrderPhaseRegisterState t s r)

private theorem generalOrderPhaseRegisterDistribution_eq_qpe_probOutcome (t s r : ℕ)
    (j : Fin (2 ^ t)) :
    generalOrderPhaseRegisterDistribution t s r j =
      PureState.probOutcome
        ((invQFT t).apply (phasePureState t ((s : ℝ) / r))) j := by
  rfl

/-- Geometric-sum amplitude for a general-order eigenphase `s/r`. -/
def generalOrderPhaseRegisterAmplitude (t s r : ℕ) (j : Fin (2 ^ t)) : ℂ :=
  phaseRegisterGeometricAmplitude t (generalOrderEigenphase s r) j

theorem generalOrderPhaseRegisterState_apply_geometricAmplitude (t s r : ℕ)
    (j : Fin (2 ^ t)) :
    (generalOrderPhaseRegisterState t s r : StateVector (Qubits t)) j =
      generalOrderPhaseRegisterAmplitude t s r j := by
  exact invQFT_phaseState_apply_geometricSum t (generalOrderEigenphase s r) j

private theorem generalOrderPhaseRegisterDistribution_eq_normSq_geometricAmplitude
    (t s r : ℕ) (j : Fin (2 ^ t)) :
    generalOrderPhaseRegisterDistribution t s r j =
      ‖generalOrderPhaseRegisterAmplitude t s r j‖ ^ 2 := by
  change StateVector.probOutcome
      (generalOrderPhaseRegisterState t s r : StateVector (Qubits t)) j =
    ‖generalOrderPhaseRegisterAmplitude t s r j‖ ^ 2
  rw [StateVector.probOutcome, generalOrderPhaseRegisterState_apply_geometricAmplitude]

/-- A phase-register outcome is good when its dyadic estimate is within the
continued-fraction recovery radius around the eigenphase `s/r`. -/
def IsGoodPhaseRegisterOutcome (t s r : ℕ) (j : Fin (2 ^ t)) : Prop :=
  |(j.val : ℝ) / (2 : ℝ) ^ t - generalOrderEigenphase s r| <
    1 / (2 * (r : ℝ) ^ 2)

private theorem goodPhaseRegisterOutcome_error_bound {t s r : ℕ} {j : Fin (2 ^ t)}
    (hgood : IsGoodPhaseRegisterOutcome t s r j) :
    |(j.val : ℝ) / (2 : ℝ) ^ t - generalOrderEigenphase s r| <
      1 / (2 * (r : ℝ) ^ 2) :=
  hgood

/-- Shor's nearest-fraction condition `|c/q - d/r| ≤ 1/(2q)` implies the
continued-fraction recovery radius used by the Lean good-outcome predicate when
the phase register size satisfies `q > r^2`. -/
theorem shorNearestFraction_isGoodPhaseRegisterOutcome {t d r : ℕ}
    {j : Fin (2 ^ t)} (hr : 0 < r)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      |(j.val : ℝ) / (2 : ℝ) ^ t - (d : ℝ) / r| ≤
        1 / (2 * (2 : ℝ) ^ t)) :
    IsGoodPhaseRegisterOutcome t d r j := by
  unfold IsGoodPhaseRegisterOutcome generalOrderEigenphase
  refine lt_of_le_of_lt hnear ?_
  have hden :
      2 * (r : ℝ) ^ 2 < 2 * (2 : ℝ) ^ t := by
    nlinarith
  have hpos : 0 < 2 * (r : ℝ) ^ 2 := by
    positivity
  exact one_div_lt_one_div_of_lt hpos hden

/-- A good phase-register outcome supplies the continued-fraction denominator
recovery condition for the true reduced phase `s/r`. -/
theorem goodPhaseRegisterOutcome_denominatorRecovery {t s r : ℕ}
    {j : Fin (2 ^ t)} (hr : 0 < r) (hsr : Nat.Coprime s r)
    (hgood : IsGoodPhaseRegisterOutcome t s r j) :
    ∃ n,
      (s : ℚ) / (r : ℚ) =
        (((j.val : ℝ) / (2 : ℝ) ^ t).convergent n) ∧
      ((((j.val : ℝ) / (2 : ℝ) ^ t).convergent n).den = r) := by
  exact
    RationalApproximation.denominatorRecovery_of_phaseEstimate
      (ξ := (j.val : ℝ) / (2 : ℝ) ^ t) (s := s) (r := r) hr hsr
      (by simpa [IsGoodPhaseRegisterOutcome, generalOrderEigenphase] using hgood)

/-- Total probability mass assigned to good phase-register outcomes. -/
noncomputable def goodPhaseRegisterOutcomeMass (t s r : ℕ) : ℝ :=
  by
    classical
    exact
      ∑ j : Fin (2 ^ t),
        if IsGoodPhaseRegisterOutcome t s r j then
          generalOrderPhaseRegisterDistribution t s r j
        else
          0

private theorem goodPhaseRegisterOutcomeMass_nonneg (t s r : ℕ) :
    0 ≤ goodPhaseRegisterOutcomeMass t s r := by
  classical
  unfold goodPhaseRegisterOutcomeMass
  exact Finset.sum_nonneg fun j _ => by
    by_cases hgood : IsGoodPhaseRegisterOutcome t s r j
    · simpa [hgood] using generalOrderPhaseRegisterDistribution_nonneg t s r j
    · simp [hgood]

/-- Aggregate good-outcome lower bound from explicit per-outcome lower bounds.
The analytic estimate for a concrete set of good outcomes can be supplied
separately, while this theorem fixes the probability-composition interface. -/
private theorem goodPhaseRegisterOutcomeMass_lowerBound_of_pointwise
    (t s r : ℕ) (J : Finset (Fin (2 ^ t))) {c : ℝ}
    (_hc : 0 ≤ c)
    (hgood : ∀ j, j ∈ J → IsGoodPhaseRegisterOutcome t s r j)
    (hprob : ∀ j, j ∈ J → c ≤ generalOrderPhaseRegisterDistribution t s r j) :
    (J.card : ℝ) * c ≤ goodPhaseRegisterOutcomeMass t s r := by
  classical
  calc
    (J.card : ℝ) * c = J.sum (fun _j => c) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ J.sum (fun j => generalOrderPhaseRegisterDistribution t s r j) := by
      exact Finset.sum_le_sum fun j hj => hprob j hj
    _ = J.sum (fun j =>
        if IsGoodPhaseRegisterOutcome t s r j then
          generalOrderPhaseRegisterDistribution t s r j
        else
          0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [hgood j hj]
    _ ≤ Finset.univ.sum (fun j : Fin (2 ^ t) =>
        if IsGoodPhaseRegisterOutcome t s r j then
          generalOrderPhaseRegisterDistribution t s r j
        else
          0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (by intro j _; simp) ?_
      intro j _ _hj_not
      by_cases hgoodj : IsGoodPhaseRegisterOutcome t s r j
      · simpa [hgoodj] using generalOrderPhaseRegisterDistribution_nonneg t s r j
      · simp [hgoodj]
    _ = goodPhaseRegisterOutcomeMass t s r := by
      rfl

/-! ### Shor-style source success lower bound -/

/-- Source-level count of recoverable measurement states in Shor's general
order-finding analysis: `r` possible target residues times `φ(r)` coprime
fractions. -/
def shorRecoverableStateCount (r : ℕ) : ℕ :=
  r * Nat.totient r

/-- Numerators `d` with `0 ≤ d < r` and `gcd(d,r)=1`, matching the coprime
fractions counted in Shor's order-recovery analysis. -/
def shorRecoverableFractionIndices (r : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun d => r.Coprime d.val

/-- Source-level two-register recoverable states are indexed by an orbit
coordinate `k < r` and a coprime fraction numerator `d`. -/
abbrev ShorRecoverableStateIndex (r : ℕ) :=
  Fin r × Fin r

/-- Finite index set for Shor's source-level recoverable measurement states. -/
def shorRecoverableStateIndices (r : ℕ) :
    Finset (ShorRecoverableStateIndex r) :=
  Finset.univ.product (shorRecoverableFractionIndices r)

theorem card_shorRecoverableFractionIndices (r : ℕ) :
    (shorRecoverableFractionIndices r).card = Nat.totient r := by
  rw [Nat.totient_eq_card_coprime]
  refine Finset.card_bij (fun d _ => d.val) ?_ ?_ ?_
  · intro d hd
    have hcop : r.Coprime d.val := by
      simpa only [shorRecoverableFractionIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] using hd
    simpa only [Finset.mem_filter, Finset.mem_range] using And.intro d.isLt hcop
  · intro d _ e _ h
    exact Fin.ext h
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    refine ⟨⟨d, hd.1⟩, ?_, rfl⟩
    simpa [shorRecoverableFractionIndices] using hd.2

theorem card_shorRecoverableStateIndices (r : ℕ) :
    (shorRecoverableStateIndices r).card = shorRecoverableStateCount r := by
  simp [shorRecoverableStateIndices, shorRecoverableStateCount,
    ShorRecoverableStateIndex, card_shorRecoverableFractionIndices]

/-- Source-level pointwise probability lower bound for each recoverable
two-register measurement state in Shor's analysis. -/
def shorRecoverableStatePointwiseLowerBound (r : ℕ) : ℝ :=
  1 / (3 * (r : ℝ) ^ 2)

/-- Per-numerator success lower bound obtained by summing Shor's source
pointwise lower bound over the `r` orbit coordinates attached to one coprime
fraction numerator. -/
def shorSingleNumeratorSuccessLowerBound (r : ℕ) : ℝ :=
  (r : ℝ) * shorRecoverableStatePointwiseLowerBound r

/-- Source-level aggregate success lower bound obtained from the recoverable
state count and pointwise state lower bound in Shor's analysis. -/
def shorOrderRecoverySuccessLowerBound (r : ℕ) : ℝ :=
  (Nat.totient r : ℝ) / (3 * (r : ℝ))

theorem shorRecoverableStatePointwiseLowerBound_nonneg (r : ℕ) :
    0 ≤ shorRecoverableStatePointwiseLowerBound r := by
  unfold shorRecoverableStatePointwiseLowerBound
  positivity

private theorem shorSingleNumeratorSuccessLowerBound_nonneg (r : ℕ) :
    0 ≤ shorSingleNumeratorSuccessLowerBound r := by
  unfold shorSingleNumeratorSuccessLowerBound
  exact mul_nonneg (Nat.cast_nonneg r)
    (shorRecoverableStatePointwiseLowerBound_nonneg r)

private theorem shorOrderRecoverySuccessLowerBound_nonneg (r : ℕ) :
    0 ≤ shorOrderRecoverySuccessLowerBound r := by
  unfold shorOrderRecoverySuccessLowerBound
  positivity

/-- The source count `r * φ(r)` and pointwise lower bound `1/(3r^2)` multiply
to Shor's stated order-recovery lower bound `φ(r)/(3r)`. -/
theorem shorRecoverableStateCount_mul_pointwiseLowerBound_eq_successLowerBound
    {r : ℕ} (hr : 0 < r) :
    (shorRecoverableStateCount r : ℝ) *
        shorRecoverableStatePointwiseLowerBound r =
      shorOrderRecoverySuccessLowerBound r := by
  unfold shorRecoverableStateCount shorRecoverableStatePointwiseLowerBound
    shorOrderRecoverySuccessLowerBound
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Nat.cast_mul]
  field_simp [hrR]

/-- The recoverable coprime-numerator count times the per-numerator success
lower bound is Shor's aggregate order-recovery lower bound. -/
private theorem recoverableFractionCount_mul_singleSuccess_eq_orderRecovery
    {r : ℕ} (hr : 0 < r) :
    ((shorRecoverableFractionIndices r).card : ℝ) *
        shorSingleNumeratorSuccessLowerBound r =
      shorOrderRecoverySuccessLowerBound r := by
  rw [card_shorRecoverableFractionIndices]
  unfold shorSingleNumeratorSuccessLowerBound
  calc
    (Nat.totient r : ℝ) *
        ((r : ℝ) * shorRecoverableStatePointwiseLowerBound r) =
        ((r * Nat.totient r : ℕ) : ℝ) *
          shorRecoverableStatePointwiseLowerBound r := by
      rw [Nat.cast_mul]
      ring
    _ = (shorRecoverableStateCount r : ℝ) *
          shorRecoverableStatePointwiseLowerBound r := by
      rfl
    _ = shorOrderRecoverySuccessLowerBound r :=
      shorRecoverableStateCount_mul_pointwiseLowerBound_eq_successLowerBound hr

/-- Generic aggregation bridge for the Shor 1995 order-recovery count: if a
finite event set has the source recoverable-state cardinality and every event
has the source pointwise lower bound, then the total probability mass is at
least `φ(r)/(3r)`. The analytic construction of the event set is kept as the
caller-supplied premise. -/
private theorem shorOrderRecoverySuccessLowerBound_le_totalMass_of_sourceEvents
    {Ω : Type*} [Fintype Ω] (prob : Ω → ℝ)
    (J : Finset Ω) {r : ℕ} (hr : 0 < r)
    (hcard : J.card = shorRecoverableStateCount r)
    (hpoint :
      ∀ ω, ω ∈ J → shorRecoverableStatePointwiseLowerBound r ≤ prob ω)
    (hnonneg_outside : ∀ ω, ω ∉ J → 0 ≤ prob ω) :
    shorOrderRecoverySuccessLowerBound r ≤ ∑ ω, prob ω := by
  calc
    shorOrderRecoverySuccessLowerBound r =
        (shorRecoverableStateCount r : ℝ) *
          shorRecoverableStatePointwiseLowerBound r := by
      exact (shorRecoverableStateCount_mul_pointwiseLowerBound_eq_successLowerBound
        (r := r) hr).symm
    _ = (J.card : ℝ) * shorRecoverableStatePointwiseLowerBound r := by
      rw [hcard]
    _ = J.sum fun _ω => shorRecoverableStatePointwiseLowerBound r := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ J.sum prob := by
      exact Finset.sum_le_sum fun ω hω => hpoint ω hω
    _ ≤ Finset.univ.sum prob := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (by intro ω _; simp) ?_
      intro ω _ hω
      exact hnonneg_outside ω hω

/-- Joint source outcome used in Shor's source-level order-recovery count: a
phase-register value together with the orbit/target-register coordinate. -/
abbrev ShorSourceJointOutcome (t r : ℕ) :=
  Fin (2 ^ t) × Fin r

/-- Recoverable joint outcomes obtained by assigning a phase-register event to
each coprime numerator `d` and pairing it with every orbit coordinate. -/
def shorSourceJointRecoverableEvents {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t)) :
    Finset (ShorSourceJointOutcome t r) :=
  (shorRecoverableStateIndices r).image fun idx => (eventOf idx.2, idx.1)

/-! ### Public output-event vocabulary -/

/-- A continued-fraction denominator candidate extracted from the phase-register
component of a source joint outcome. This records the classical post-processing
search result without mentioning the true order
[Sho95, source.tex:1614-1633] [dW19, qcnotes.tex:2293-2301]. -/
def orderFindingContinuedFractionCandidate {t r : ℕ}
    (outcome : ShorSourceJointOutcome t r) (candidate : ℕ) : Prop :=
  ∃ n, (((outcome.1.val : ℝ) / (2 : ℝ) ^ t).convergent n).den = candidate

/-- A public order-finding output candidate: the continued-fraction stage
produces the candidate denominator, and the classical validation stage accepts
it as a minimal power return for the supplied group element. -/
def orderFindingValidatedOutputCandidate {G : Type*} [Monoid G] {t r : ℕ}
    (g : G) (outcome : ShorSourceJointOutcome t r) (candidate : ℕ) : Prop :=
  orderFindingContinuedFractionCandidate outcome candidate ∧
    OrderCandidate.IsMinimalPowerReturn g candidate

/-- Public output-success event for order finding: the validated classical
post-processing output is the true order `r`
[Sho95, source.tex:1614-1633] [dW19, qcnotes.tex:2293-2301]. -/
def orderFindingOutputSuccessEvent {G : Type*} [Monoid G] {t r : ℕ}
    (g : G) (outcome : ShorSourceJointOutcome t r) : Prop :=
  ∃ candidate,
    orderFindingValidatedOutputCandidate g outcome candidate ∧ candidate = r

/-- Public lower bound for the order-finding output-success probability. -/
def orderFindingOutputSuccessLowerBound (r : ℕ) : ℝ :=
  (Nat.totient r : ℝ) / (3 * (r : ℝ))

@[simp]
theorem orderFindingOutputSuccessLowerBound_eq_shor (r : ℕ) :
    orderFindingOutputSuccessLowerBound r =
      shorOrderRecoverySuccessLowerBound r :=
  rfl

/-- Probability mass assigned to public order-finding output-success events. -/
noncomputable def orderFindingOutputSuccessMass {G : Type*} [Monoid G] {t r : ℕ}
    (g : G) (prob : ShorSourceJointOutcome t r → ℝ) : ℝ :=
  by
    classical
    exact
      ∑ outcome : ShorSourceJointOutcome t r,
        if orderFindingOutputSuccessEvent g outcome then prob outcome else 0

theorem orderFindingOutputSuccessEvent.of_denominator_and_orderOf
    {G : Type*} [Monoid G] {g : G} {t r : ℕ}
    {outcome : ShorSourceJointOutcome t r}
    (hcf : orderFindingContinuedFractionCandidate outcome r)
    (hr : 0 < r) (horder : orderOf g = r) :
    orderFindingOutputSuccessEvent g outcome := by
  refine ⟨r, ⟨hcf, ?_⟩, rfl⟩
  exact OrderCandidate.isMinimalPowerReturn_of_orderOf_eq hr horder

theorem shorRecoverableEvents_subset_orderFindingOutputSuccessEvent
    {G : Type*} [Monoid G] {g : G} {t r : ℕ}
    {eventOf : Fin r → Fin (2 ^ t)}
    (hcf : ∀ outcome,
      outcome ∈ shorSourceJointRecoverableEvents (t := t) (r := r) eventOf →
        orderFindingContinuedFractionCandidate outcome r)
    (hr : 0 < r) (horder : orderOf g = r) :
    ∀ outcome,
      outcome ∈ shorSourceJointRecoverableEvents (t := t) (r := r) eventOf →
        orderFindingOutputSuccessEvent g outcome := by
  intro outcome houtcome
  exact orderFindingOutputSuccessEvent.of_denominator_and_orderOf
    (hcf outcome houtcome) hr horder

theorem shorOrderRecoverySuccessLowerBound_le_outputSuccessMass_of_recoverableEvents
    {G : Type*} [Monoid G] {g : G} {t r : ℕ}
    {eventOf : Fin r → Fin (2 ^ t)}
    (prob : ShorSourceJointOutcome t r → ℝ)
    (hcf : ∀ outcome,
      outcome ∈ shorSourceJointRecoverableEvents (t := t) (r := r) eventOf →
        orderFindingContinuedFractionCandidate outcome r)
    (hr : 0 < r) (horder : orderOf g = r)
    (hmass : shorOrderRecoverySuccessLowerBound r ≤
      (shorSourceJointRecoverableEvents (t := t) (r := r) eventOf).sum prob)
    (hnonneg : ∀ outcome, 0 ≤ prob outcome) :
    shorOrderRecoverySuccessLowerBound r ≤
      orderFindingOutputSuccessMass g prob := by
  classical
  have hsubset :=
    shorRecoverableEvents_subset_orderFindingOutputSuccessEvent
      (g := g) hcf hr horder
  calc
    shorOrderRecoverySuccessLowerBound r ≤
        (shorSourceJointRecoverableEvents (t := t) (r := r) eventOf).sum prob :=
      hmass
    _ =
        (shorSourceJointRecoverableEvents (t := t) (r := r) eventOf).sum
          (fun outcome =>
            if orderFindingOutputSuccessEvent g outcome then prob outcome else 0) := by
      refine Finset.sum_congr rfl fun outcome houtcome => ?_
      simp [hsubset outcome houtcome]
    _ ≤
        Finset.univ.sum
          (fun outcome : ShorSourceJointOutcome t r =>
            if orderFindingOutputSuccessEvent g outcome then prob outcome else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (by intro outcome _; simp) ?_
      intro outcome _ _hnot
      by_cases hsuccess : orderFindingOutputSuccessEvent g outcome
      · simpa [hsuccess] using hnonneg outcome
      · simp [hsuccess]
    _ = orderFindingOutputSuccessMass g prob := by
      simp [orderFindingOutputSuccessMass]

/-- Source-side arithmetic progression of exponent-register values whose
residue modulo the order is the selected orbit coordinate. -/
def shorSourceJointPreimageIndices (t : ℕ) {r : ℕ} (k : Fin r) :
    Finset (Fin (2 ^ t)) :=
  Finset.univ.filter fun a => a.val % r = k.val

/-- Quotient indices for source exponents in one Shor orbit residue class:
`a = k + r*b` while staying inside the phase-register range. -/
def shorSourceJointQuotientIndices (t : ℕ) {r : ℕ} (k : Fin r) :
    Finset ℕ :=
  (Finset.range (2 ^ t)).filter fun b => k.val + r * b < 2 ^ t

/-- Reconstruct a phase-register exponent from a quotient index. Outside the
legal quotient range this returns `0`, so callers can use it as a total
function in finite sums while proving the precise value on the quotient set. -/
def shorSourceJointExponentOfQuotient (t : ℕ) {r : ℕ}
    (k : Fin r) (b : ℕ) : Fin (2 ^ t) :=
  if hb : k.val + r * b < 2 ^ t then
    ⟨k.val + r * b, hb⟩
  else
    ⟨0, pow_pos (by norm_num) t⟩

@[simp]
theorem mem_shorSourceJointPreimageIndices {t r : ℕ} {k : Fin r}
    {a : Fin (2 ^ t)} :
    a ∈ shorSourceJointPreimageIndices t k ↔ a.val % r = k.val := by
  simp [shorSourceJointPreimageIndices]

@[simp]
theorem mem_shorSourceJointQuotientIndices {t r : ℕ} {k : Fin r}
    {b : ℕ} :
    b ∈ shorSourceJointQuotientIndices t k ↔
      b < 2 ^ t ∧ k.val + r * b < 2 ^ t := by
  simp [shorSourceJointQuotientIndices]

/-- Under positive order, the explicit phase-register range bound in the
quotient-index definition is redundant. -/
theorem mem_shorSourceJointQuotientIndices_iff_orbit_add_order_mul_lt
    {t r : ℕ} (hr : 0 < r) {k : Fin r} {b : ℕ} :
    b ∈ shorSourceJointQuotientIndices t k ↔
      k.val + r * b < 2 ^ t := by
  rw [mem_shorSourceJointQuotientIndices]
  constructor
  · exact And.right
  · intro hb
    constructor
    · have hr_ge_one : 1 ≤ r := Nat.succ_le_iff.mpr hr
      have hb_le : b ≤ k.val + r * b := by
        calc
          b = 1 * b := by simp
          _ ≤ r * b := Nat.mul_le_mul_right b hr_ge_one
          _ ≤ k.val + r * b := Nat.le_add_left _ _
      exact lt_of_le_of_lt hb_le hb
    · exact hb

/-- The quotient-index set for one source orbit is the initial range of all
legal quotients. This is the Shor-specific range form needed before applying a
finite geometric-sum estimate. -/
theorem shorSourceJointQuotientIndices_eq_range
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t) :
    shorSourceJointQuotientIndices t k =
      Finset.range (((2 ^ t - 1 - k.val) / r) + 1) := by
  apply Finset.ext
  intro b
  rw [mem_shorSourceJointQuotientIndices_iff_orbit_add_order_mul_lt hr]
  simp only [Finset.mem_range]
  constructor
  · intro hb
    have hb_le_pred : k.val + r * b ≤ 2 ^ t - 1 := Nat.le_pred_of_lt hb
    have hmul_le : r * b ≤ 2 ^ t - 1 - k.val := by
      omega
    have hb_div : b ≤ (2 ^ t - 1 - k.val) / r := by
      exact (Nat.le_div_iff_mul_le hr).mpr (by
        simpa [mul_comm] using hmul_le)
    exact Nat.lt_succ_of_le hb_div
  · intro hb
    have hb_le_div : b ≤ (2 ^ t - 1 - k.val) / r :=
      Nat.lt_succ_iff.mp hb
    have hmul_le : r * b ≤ 2 ^ t - 1 - k.val := by
      have hmul_le' : b * r ≤ 2 ^ t - 1 - k.val :=
        (Nat.le_div_iff_mul_le hr).mp hb_le_div
      simpa [mul_comm] using hmul_le'
    have hk_le_pred : k.val ≤ 2 ^ t - 1 := Nat.le_pred_of_lt hkq
    have hle_pred : k.val + r * b ≤ 2 ^ t - 1 := by
      omega
    have hq_pos : 0 < 2 ^ t := pow_pos (by norm_num) t
    omega

/-- Cardinality of one Shor source orbit's quotient-index set. -/
private theorem card_shorSourceJointQuotientIndices
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t) :
    (shorSourceJointQuotientIndices t k).card =
      ((2 ^ t - 1 - k.val) / r) + 1 := by
  rw [shorSourceJointQuotientIndices_eq_range hr hkq]
  exact Finset.card_range _

/-- The finite largeness premise used by the source-faithful Shor lower-bound
route ensures every orbit offset fits in the phase-register range. -/
theorem shorSourceJointOrbit_lt_phaseRegister_of_large
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t) (k : Fin r) :
    k.val < 2 ^ t := by
  omega

/-- Under the finite largeness premise used by the source-faithful Shor
lower-bound route, the number of source exponents in one orbit residue class is
within a `13/12` and `11/12` multiplicative window after scaling by `r / 2^t`.
This quotient-length estimate is the arithmetic input to the later sine-ratio
bound. -/
theorem shorSourceJointQuotientLength_scaled_bounds
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t) (k : Fin r) :
    let m : ℕ := ((2 ^ t - 1 - k.val) / r) + 1
    (11 / 12 : ℝ) ≤ ((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t ∧
      ((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t ≤ (13 / 12 : ℝ) := by
  let q : ℕ := 2 ^ t
  let m : ℕ := ((q - 1 - k.val) / r) + 1
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hlarge_q : 12 * r ≤ q := by
    simpa [q] using hlarge
  have hkq : k.val < q := by
    simpa [q] using shorSourceJointOrbit_lt_phaseRegister_of_large hlarge k
  have hq_ge_r : r ≤ q := by omega
  have hdiv_upper :
      ((q - 1 - k.val) / r) * r ≤ q - 1 - k.val :=
    Nat.div_mul_le_self (q - 1 - k.val) r
  have hn_le_q : q - 1 - k.val ≤ q := by
    omega
  have hupper_nat : m * r ≤ q + r := by
    dsimp [m]
    calc
      (((q - 1 - k.val) / r) + 1) * r =
          ((q - 1 - k.val) / r) * r + r := by
        rw [Nat.add_mul, one_mul]
      _ ≤ (q - 1 - k.val) + r := by
        exact Nat.add_le_add_right hdiv_upper r
      _ ≤ q + r := by
        exact Nat.add_le_add_right hn_le_q r
  have hmod_lt :
      (q - 1 - k.val) % r < r :=
    Nat.mod_lt _ hr
  have hquotient_strict :
      q - 1 - k.val < m * r := by
    dsimp [m]
    calc
      q - 1 - k.val =
          (q - 1 - k.val) % r + r * ((q - 1 - k.val) / r) := by
        exact (Nat.mod_add_div (q - 1 - k.val) r).symm
      _ < r + r * ((q - 1 - k.val) / r) := by
        exact Nat.add_lt_add_right hmod_lt _
      _ = (((q - 1 - k.val) / r) + 1) * r := by
        ring
  have hk_le_r : k.val ≤ r := le_of_lt k.isLt
  have hq_sub_k_le : q - k.val ≤ m * r := by
    have hsucc := Nat.succ_le_of_lt hquotient_strict
    omega
  have hlower_nat : q ≤ m * r + r := by
    omega
  have hqR_pos : 0 < (q : ℝ) := by
    exact_mod_cast hq_pos
  have hlargeR : (12 : ℝ) * (r : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hlarge_q
  have hupperR : ((m * r : ℕ) : ℝ) ≤ (q : ℝ) + (r : ℝ) := by
    exact_mod_cast hupper_nat
  have hlowerR : (q : ℝ) ≤ ((m * r : ℕ) : ℝ) + (r : ℝ) := by
    exact_mod_cast hlower_nat
  have hscaled_lower : (11 / 12 : ℝ) * (q : ℝ) ≤ ((m * r : ℕ) : ℝ) := by
    nlinarith
  have hscaled_upper : ((m * r : ℕ) : ℝ) ≤ (13 / 12 : ℝ) * (q : ℝ) := by
    nlinarith
  have htarget :
      (11 / 12 : ℝ) ≤ ((m : ℝ) * (r : ℝ)) / (q : ℝ) ∧
        ((m : ℝ) * (r : ℝ)) / (q : ℝ) ≤ (13 / 12 : ℝ) := by
    constructor
    · rw [le_div_iff₀ hqR_pos]
      simpa [Nat.cast_mul] using hscaled_lower
    · rw [div_le_iff₀ hqR_pos]
      simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hscaled_upper
  simpa [q, m, Nat.cast_pow] using htarget

@[simp]
theorem shorSourceJointExponentOfQuotient_val_of_mem
    {t r : ℕ} {k : Fin r} {b : ℕ}
    (hb : b ∈ shorSourceJointQuotientIndices t k) :
    (shorSourceJointExponentOfQuotient t k b).val = k.val + r * b := by
  simp [shorSourceJointExponentOfQuotient,
    (mem_shorSourceJointQuotientIndices.mp hb).2]

theorem shorSourceJointExponentOfQuotient_mem_preimageIndices
    {t r : ℕ} {k : Fin r} {b : ℕ}
    (hb : b ∈ shorSourceJointQuotientIndices t k) :
    shorSourceJointExponentOfQuotient t k b ∈
      shorSourceJointPreimageIndices t k := by
  rw [mem_shorSourceJointPreimageIndices]
  rw [shorSourceJointExponentOfQuotient_val_of_mem hb]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt k.isLt

/-- Residue-class normal form for source exponents in one Shor orbit. -/
theorem shorSourceJointPreimageIndices_val_eq_orbit_add_order_mul_div
    {t r : ℕ} {k : Fin r} {a : Fin (2 ^ t)}
    (ha : a ∈ shorSourceJointPreimageIndices t k) :
    a.val = k.val + r * (a.val / r) := by
  calc
    a.val = a.val % r + r * (a.val / r) := (Nat.mod_add_div a.val r).symm
    _ = k.val + r * (a.val / r) := by
      rw [(mem_shorSourceJointPreimageIndices.mp ha)]

/-- Membership in a Shor source preimage class is equivalent to having the
selected orbit offset plus an order-spaced quotient. -/
private theorem mem_shorSourceJointPreimageIndices_iff_exists_order_quotient
    {t r : ℕ} {k : Fin r} {a : Fin (2 ^ t)} :
    a ∈ shorSourceJointPreimageIndices t k ↔
      ∃ b : ℕ, a.val = k.val + r * b := by
  constructor
  · intro ha
    exact ⟨a.val / r,
      shorSourceJointPreimageIndices_val_eq_orbit_add_order_mul_div ha⟩
  · rintro ⟨b, h⟩
    rw [mem_shorSourceJointPreimageIndices, h]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt k.isLt

/-- Reconstruct the phase-register exponent from a quotient in one source
orbit residue class. -/
theorem mk_mem_shorSourceJointPreimageIndices_of_orbit_add_order_mul_lt
    {t r : ℕ} {k : Fin r} {b : ℕ}
    (hb : k.val + r * b < 2 ^ t) :
    (⟨k.val + r * b, hb⟩ : Fin (2 ^ t)) ∈
      shorSourceJointPreimageIndices t k := by
  rw [mem_shorSourceJointPreimageIndices]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt k.isLt

/-- The quotient normal form of a source preimage exponent stays inside the
phase-register range. -/
theorem shorSourceJointPreimageIndices_orbit_add_order_mul_div_lt
    {t r : ℕ} {k : Fin r} {a : Fin (2 ^ t)}
    (ha : a ∈ shorSourceJointPreimageIndices t k) :
    k.val + r * (a.val / r) < 2 ^ t := by
  rw [← shorSourceJointPreimageIndices_val_eq_orbit_add_order_mul_div ha]
  exact a.isLt

/-- A source preimage exponent determines a quotient index in the same orbit
residue class. -/
theorem shorSourceJointPreimageIndices_div_mem_quotientIndices
    {t r : ℕ} {k : Fin r} {a : Fin (2 ^ t)}
    (ha : a ∈ shorSourceJointPreimageIndices t k) :
    a.val / r ∈ shorSourceJointQuotientIndices t k := by
  rw [mem_shorSourceJointQuotientIndices]
  constructor
  · exact lt_of_le_of_lt (Nat.div_le_self a.val r) a.isLt
  · exact shorSourceJointPreimageIndices_orbit_add_order_mul_div_lt ha

/-- Rebuilding a source exponent from the quotient determined by a preimage
element returns the same phase-register index value. -/
private theorem shorSourceJointPreimageIndices_orbit_add_order_mul_div_val
    {t r : ℕ} {k : Fin r} {a : Fin (2 ^ t)}
    (ha : a ∈ shorSourceJointPreimageIndices t k) :
    (⟨k.val + r * (a.val / r),
      shorSourceJointPreimageIndices_orbit_add_order_mul_div_lt ha⟩ :
        Fin (2 ^ t)).val = a.val := by
  exact (shorSourceJointPreimageIndices_val_eq_orbit_add_order_mul_div ha).symm

/-- Dividing a reconstructed source exponent by the order recovers its
quotient index. -/
theorem shorSourceJointPreimageIndices_orbit_add_order_mul_div
    {t r : ℕ} (hr : 0 < r) {k : Fin r} {b : ℕ}
    (hb : k.val + r * b < 2 ^ t) :
    (⟨k.val + r * b, hb⟩ : Fin (2 ^ t)).val / r = b := by
  rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt k.isLt, Nat.zero_add]

/-- A quotient index reconstructs a source preimage exponent in the same orbit
residue class. -/
private theorem shorSourceJointQuotientIndices_mk_mem_preimageIndices
    {t r : ℕ} {k : Fin r} {b : ℕ}
    (hb : b ∈ shorSourceJointQuotientIndices t k) :
    (⟨k.val + r * b, (mem_shorSourceJointQuotientIndices.mp hb).2⟩ :
        Fin (2 ^ t)) ∈ shorSourceJointPreimageIndices t k :=
  mk_mem_shorSourceJointPreimageIndices_of_orbit_add_order_mul_lt
    (mem_shorSourceJointQuotientIndices.mp hb).2

/-- Reindex a source preimage sum by the quotient `b` in the normal form
`a = k + r*b`. -/
theorem sum_shorSourceJointPreimageIndices_eq_sum_quotientIndices
    {M : Type*} [AddCommMonoid M] {t r : ℕ} (hr : 0 < r)
    (k : Fin r) (f : Fin (2 ^ t) → M) :
    (shorSourceJointPreimageIndices t k).sum f =
      (shorSourceJointQuotientIndices t k).sum
        (fun b => f (shorSourceJointExponentOfQuotient t k b)) := by
  refine Finset.sum_bij
    (fun a ha => a.val / r) ?hi ?hinj ?hsurj ?h
  · intro a ha
    exact shorSourceJointPreimageIndices_div_mem_quotientIndices ha
  · intro a ha a' ha' hdiv
    apply Fin.ext
    calc
      a.val = k.val + r * (a.val / r) :=
        shorSourceJointPreimageIndices_val_eq_orbit_add_order_mul_div ha
      _ = k.val + r * (a'.val / r) := by rw [hdiv]
      _ = a'.val :=
        (shorSourceJointPreimageIndices_val_eq_orbit_add_order_mul_div ha').symm
  · intro b hb
    refine ⟨shorSourceJointExponentOfQuotient t k b,
      shorSourceJointExponentOfQuotient_mem_preimageIndices hb, ?_⟩
    rw [shorSourceJointExponentOfQuotient_val_of_mem hb]
    exact shorSourceJointPreimageIndices_orbit_add_order_mul_div hr
      (mem_shorSourceJointQuotientIndices.mp hb).2
  · intro a ha
    apply congrArg f
    apply Fin.ext
    rw [shorSourceJointExponentOfQuotient_val_of_mem
      (shorSourceJointPreimageIndices_div_mem_quotientIndices ha)]
    exact shorSourceJointPreimageIndices_val_eq_orbit_add_order_mul_div ha

/-- Single source-sum phase term for observing phase-register value `c` from
source exponent `a`. -/
def shorSourceJointPhaseTerm (t : ℕ) (c a : Fin (2 ^ t)) : ℂ :=
  Complex.exp (2 * Real.pi *
    ((((a.val : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t : ℝ)) *
      Complex.I)

/-- On a legal quotient index, the source phase term splits into the orbit
offset phase and the quotient-step phase. -/
theorem shorSourceJointPhaseTerm_exponentOfQuotient_eq_orbit_mul_step
    {t r : ℕ} {k : Fin r} {b : ℕ} {c : Fin (2 ^ t)}
    (hb : b ∈ shorSourceJointQuotientIndices t k) :
    shorSourceJointPhaseTerm t c
        (shorSourceJointExponentOfQuotient t k b) =
      Complex.exp (2 * Real.pi *
          ((((k.val : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t : ℝ)) *
            Complex.I) *
        Complex.exp (2 * Real.pi *
          (((((r : ℝ) * (b : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t) : ℝ)) *
            Complex.I) := by
  unfold shorSourceJointPhaseTerm
  rw [shorSourceJointExponentOfQuotient_val_of_mem hb]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Shor-style source joint amplitude for observing phase-register value `c`
and orbit coordinate `k`. This is only the concrete source-sum shape; lower
bounds for recoverable events remain explicit certificate obligations. -/
def shorSourceJointAmplitude (t r : ℕ)
    (outcome : ShorSourceJointOutcome t r) : ℂ :=
  (((2 : ℝ) ^ t : ℂ))⁻¹ *
    (shorSourceJointPreimageIndices t outcome.2).sum fun a =>
      shorSourceJointPhaseTerm t outcome.1 a

/-- Reindexed source joint amplitude as a quotient-indexed sum. -/
theorem shorSourceJointAmplitude_eq_quotient_sum {t r : ℕ}
    (hr : 0 < r) (outcome : ShorSourceJointOutcome t r) :
    shorSourceJointAmplitude t r outcome =
      (((2 : ℝ) ^ t : ℂ))⁻¹ *
        (shorSourceJointQuotientIndices t outcome.2).sum
          (fun b => shorSourceJointPhaseTerm t outcome.1
            (shorSourceJointExponentOfQuotient t outcome.2 b)) := by
  unfold shorSourceJointAmplitude
  rw [sum_shorSourceJointPreimageIndices_eq_sum_quotientIndices hr]

/-- Reindexed and phase-factored source joint amplitude. The remaining sum is
the quotient-step geometric sum used by the analytic lower-bound pass. -/
theorem shorSourceJointAmplitude_eq_orbit_phase_mul_quotient_step_sum
    {t r : ℕ} (hr : 0 < r) (outcome : ShorSourceJointOutcome t r) :
    shorSourceJointAmplitude t r outcome =
      (((2 : ℝ) ^ t : ℂ))⁻¹ *
        (Complex.exp (2 * Real.pi *
            ((((outcome.2.val : ℝ) * (outcome.1.val : ℝ)) /
              (2 : ℝ) ^ t : ℝ)) * Complex.I) *
          (shorSourceJointQuotientIndices t outcome.2).sum
            (fun b => Complex.exp (2 * Real.pi *
              (((((r : ℝ) * (b : ℝ) * (outcome.1.val : ℝ)) /
                (2 : ℝ) ^ t) : ℝ)) * Complex.I))) := by
  rw [shorSourceJointAmplitude_eq_quotient_sum hr]
  congr 1
  calc
    (shorSourceJointQuotientIndices t outcome.2).sum
        (fun b => shorSourceJointPhaseTerm t outcome.1
          (shorSourceJointExponentOfQuotient t outcome.2 b)) =
      (shorSourceJointQuotientIndices t outcome.2).sum
        (fun b =>
          Complex.exp (2 * Real.pi *
              ((((outcome.2.val : ℝ) * (outcome.1.val : ℝ)) /
                (2 : ℝ) ^ t : ℝ)) * Complex.I) *
            Complex.exp (2 * Real.pi *
              (((((r : ℝ) * (b : ℝ) * (outcome.1.val : ℝ)) /
                (2 : ℝ) ^ t) : ℝ)) * Complex.I)) := by
        refine Finset.sum_congr rfl fun b hb => ?_
        exact shorSourceJointPhaseTerm_exponentOfQuotient_eq_orbit_mul_step hb
    _ =
      Complex.exp (2 * Real.pi *
          ((((outcome.2.val : ℝ) * (outcome.1.val : ℝ)) /
            (2 : ℝ) ^ t : ℝ)) * Complex.I) *
        (shorSourceJointQuotientIndices t outcome.2).sum
          (fun b => Complex.exp (2 * Real.pi *
            (((((r : ℝ) * (b : ℝ) * (outcome.1.val : ℝ)) /
              (2 : ℝ) ^ t) : ℝ)) * Complex.I)) := by
        rw [Finset.mul_sum]

/-- The quotient-step phase can be rewritten using the scaled phase error
`r*c/q - d`; the discarded phase is an integer multiple of `2πi`. -/
theorem shorSourceJointQuotient_step_phase_eq_drift_phase
    {t r : ℕ} (c : Fin (2 ^ t)) (d : Fin r) (b : ℕ) :
    Complex.exp (2 * Real.pi *
        (((((r : ℝ) * (b : ℝ) * (c.val : ℝ)) /
          (2 : ℝ) ^ t) : ℝ)) * Complex.I) =
      Complex.exp (2 * Real.pi *
        (((b : ℝ) * (((r : ℝ) * (c.val : ℝ)) /
          (2 : ℝ) ^ t - d.val)) : ℝ) * Complex.I) := by
  symm
  calc
    Complex.exp (2 * Real.pi *
        (((b : ℝ) * (((r : ℝ) * (c.val : ℝ)) /
          (2 : ℝ) ^ t - d.val)) : ℝ) * Complex.I) =
      Complex.exp (2 * Real.pi *
          (((b : ℝ) * (((r : ℝ) * (c.val : ℝ)) /
            (2 : ℝ) ^ t - d.val)) : ℝ) * Complex.I) * 1 := by
        rw [mul_one]
    _ =
      Complex.exp (2 * Real.pi *
          (((b : ℝ) * (((r : ℝ) * (c.val : ℝ)) /
            (2 : ℝ) ^ t - d.val)) : ℝ) * Complex.I) *
        Complex.exp (((b * d.val : ℕ) : ℂ) * (2 * Real.pi * Complex.I)) := by
        rw [Complex.exp_nat_mul_two_pi_mul_I]
    _ =
      Complex.exp
        (2 * Real.pi *
            (((b : ℝ) * (((r : ℝ) * (c.val : ℝ)) /
              (2 : ℝ) ^ t - d.val)) : ℝ) * Complex.I +
          ((b * d.val : ℕ) : ℂ) * (2 * Real.pi * Complex.I)) := by
        rw [← Complex.exp_add]
    _ =
      Complex.exp (2 * Real.pi *
        (((((r : ℝ) * (b : ℝ) * (c.val : ℝ)) /
          (2 : ℝ) ^ t) : ℝ)) * Complex.I) := by
        congr 1
        push_cast
        ring

/-- Drift-indexed quotient sum after removing the orbit phase and the integer
phase `b*d` from the source amplitude. -/
def shorSourceJointDriftSum (t r : ℕ)
    (c : Fin (2 ^ t)) (k d : Fin r) : ℂ :=
  (shorSourceJointQuotientIndices t k).sum
    (fun b => Complex.exp (2 * Real.pi *
      (((b : ℝ) * (((r : ℝ) * (c.val : ℝ)) /
        (2 : ℝ) ^ t - d.val)) : ℝ) * Complex.I))

/-- Under the finite largeness premise, the drift sum is a consecutive
geometric-style range sum. -/
theorem shorSourceJointDriftSum_eq_range_sum_of_orbit_lt_phaseRegister
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t) (c : Fin (2 ^ t)) (d : Fin r) :
    shorSourceJointDriftSum t r c k d =
      (Finset.range (((2 ^ t - 1 - k.val) / r) + 1)).sum
        (fun b => Complex.exp (2 * Real.pi *
          (((b : ℝ) * (((r : ℝ) * (c.val : ℝ)) /
            (2 : ℝ) ^ t - d.val)) : ℝ) * Complex.I)) := by
  unfold shorSourceJointDriftSum
  rw [shorSourceJointQuotientIndices_eq_range hr hkq]

/-- Under the finite largeness premise, the drift sum is a consecutive
geometric-style range sum. -/
private theorem shorSourceJointDriftSum_eq_range_sum_of_large
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t)
    (c : Fin (2 ^ t)) (k d : Fin r) :
    shorSourceJointDriftSum t r c k d =
      (Finset.range (((2 ^ t - 1 - k.val) / r) + 1)).sum
        (fun b => Complex.exp (2 * Real.pi *
          (((b : ℝ) * (((r : ℝ) * (c.val : ℝ)) /
            (2 : ℝ) ^ t - d.val)) : ℝ) * Complex.I)) := by
  exact shorSourceJointDriftSum_eq_range_sum_of_orbit_lt_phaseRegister
    (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)
    (shorSourceJointOrbit_lt_phaseRegister_of_large hlarge k) c d

/-- If the drift phase is trivial, the source drift sum is exactly the number
of quotient indices. -/
theorem shorSourceJointDriftSum_eq_card_of_orbit_lt_phaseRegister_of_base_eq_one
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t) (c : Fin (2 ^ t)) (d : Fin r)
    (hbase :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) = 1) :
    shorSourceJointDriftSum t r c k d =
      ((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℂ) := by
  rw [shorSourceJointDriftSum_eq_range_sum_of_orbit_lt_phaseRegister hr hkq]
  exact sum_range_exp_two_pi_mul_nat_mul_I_eq_natCast_of_base_eq_one
    (θ := ((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val)
    (m := ((2 ^ t - 1 - k.val) / r) + 1) hbase

/-- If the drift phase is trivial, the source drift sum is exactly the number
of quotient indices. -/
private theorem shorSourceJointDriftSum_eq_card_of_large_of_base_eq_one
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t)
    (c : Fin (2 ^ t)) (k d : Fin r)
    (hbase :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) = 1) :
    shorSourceJointDriftSum t r c k d =
      ((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℂ) := by
  exact shorSourceJointDriftSum_eq_card_of_orbit_lt_phaseRegister_of_base_eq_one
    (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)
    (shorSourceJointOrbit_lt_phaseRegister_of_large hlarge k) c d hbase

/-- Under the finite largeness premise and a nontrivial drift phase, the drift
sum has the closed finite-geometric form. -/
theorem shorSourceJointDriftSum_eq_geometric_closed_of_orbit_lt_phaseRegister
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t) (c : Fin (2 ^ t)) (d : Fin r)
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    shorSourceJointDriftSum t r c k d =
      (Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ^
            (((2 ^ t - 1 - k.val) / r) + 1) - 1) /
        (Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) - 1) := by
  rw [shorSourceJointDriftSum_eq_range_sum_of_orbit_lt_phaseRegister hr hkq]
  exact sum_range_exp_two_pi_mul_nat_mul_I_eq_geom_closed
    (θ := ((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val)
    (m := ((2 ^ t - 1 - k.val) / r) + 1) hne

/-- Under the finite largeness premise and a nontrivial drift phase, the drift
sum has the closed finite-geometric form. -/
private theorem shorSourceJointDriftSum_eq_geometric_closed_of_large
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t)
    (c : Fin (2 ^ t)) (k d : Fin r)
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    shorSourceJointDriftSum t r c k d =
      (Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ^
            (((2 ^ t - 1 - k.val) / r) + 1) - 1) /
        (Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) - 1) := by
  exact shorSourceJointDriftSum_eq_geometric_closed_of_orbit_lt_phaseRegister
    (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)
    (shorSourceJointOrbit_lt_phaseRegister_of_large hlarge k) c d hne

/-- Norm form of the nontrivial closed finite-geometric drift sum. -/
theorem norm_shorSourceJointDriftSum_eq_geometric_ratio_of_orbit_lt_phaseRegister
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t) (c : Fin (2 ^ t)) (d : Fin r)
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    ‖shorSourceJointDriftSum t r c k d‖ =
      ‖Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ^
            (((2 ^ t - 1 - k.val) / r) + 1) - 1‖ /
        ‖Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) - 1‖ := by
  rw [shorSourceJointDriftSum_eq_geometric_closed_of_orbit_lt_phaseRegister
    hr hkq c d hne]
  rw [norm_div]

/-- Norm form of the nontrivial closed finite-geometric drift sum. -/
private theorem norm_shorSourceJointDriftSum_eq_geometric_ratio_of_large
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t)
    (c : Fin (2 ^ t)) (k d : Fin r)
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    ‖shorSourceJointDriftSum t r c k d‖ =
      ‖Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ^
            (((2 ^ t - 1 - k.val) / r) + 1) - 1‖ /
        ‖Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) - 1‖ := by
  exact norm_shorSourceJointDriftSum_eq_geometric_ratio_of_orbit_lt_phaseRegister
    (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)
    (shorSourceJointOrbit_lt_phaseRegister_of_large hlarge k) c d hne

/-- Normalizing a drift sum by the phase-register dimension divides its norm
by `2^t`. -/
theorem norm_scaled_shorSourceJointDriftSum_eq
    (t r : ℕ) (c : Fin (2 ^ t)) (k d : Fin r) :
    ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖ =
      ‖shorSourceJointDriftSum t r c k d‖ / (2 : ℝ) ^ t := by
  have hq_pos : 0 < (2 : ℝ) ^ t := by
    positivity
  have hnorm_q : ‖(((2 : ℝ) ^ t : ℂ))‖ = (2 : ℝ) ^ t := by
    change ‖(2 : ℂ) ^ t‖ = (2 : ℝ) ^ t
    rw [norm_pow]
    norm_num
  rw [norm_mul, norm_inv, hnorm_q, div_eq_inv_mul, mul_comm]

/-- Normalized norm form of the nontrivial closed finite-geometric drift sum. -/
theorem norm_scaled_shorSourceJointDriftSum_eq_geometric_ratio_of_orbit_lt_phaseRegister
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t) (c : Fin (2 ^ t)) (d : Fin r)
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖ =
      (‖Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ^
            (((2 ^ t - 1 - k.val) / r) + 1) - 1‖ /
        ‖Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) - 1‖) / (2 : ℝ) ^ t := by
  rw [norm_scaled_shorSourceJointDriftSum_eq]
  rw [norm_shorSourceJointDriftSum_eq_geometric_ratio_of_orbit_lt_phaseRegister
    hr hkq c d hne]

/-- Normalized norm form of the nontrivial closed finite-geometric drift sum. -/
theorem norm_scaled_shorSourceJointDriftSum_eq_geometric_ratio_of_large
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t)
    (c : Fin (2 ^ t)) (k d : Fin r)
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖ =
      (‖Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ^
            (((2 ^ t - 1 - k.val) / r) + 1) - 1‖ /
        ‖Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) - 1‖) / (2 : ℝ) ^ t := by
  exact norm_scaled_shorSourceJointDriftSum_eq_geometric_ratio_of_orbit_lt_phaseRegister
    (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)
    (shorSourceJointOrbit_lt_phaseRegister_of_large hlarge k) c d hne

/-- Explicit normalized lower bound for the nontrivial Shor drift branch,
leaving only the source-specific real-arithmetic estimates as hypotheses. -/
private theorem lowerBound_le_norm_scaled_shorSourceJointDriftSum_of_geometric_ratio
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t)
    (c : Fin (2 ^ t)) (k d : Fin r)
    (hprincipal :
      |2 * Real.pi *
          (((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) *
            (((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val))| ≤
        Real.pi)
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    (((2 / Real.pi) *
        |2 * Real.pi *
          (((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) *
            (((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val))|) /
        |2 * Real.pi *
          (((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val)|) /
        (2 : ℝ) ^ t ≤
      ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖ := by
  have hratio :=
    geometric_phase_norm_ratio_lower_bound
      (θ := ((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val)
      (m := ((2 ^ t - 1 - k.val) / r) + 1)
      hprincipal hne
  rw [norm_scaled_shorSourceJointDriftSum_eq_geometric_ratio_of_large
    hlarge c k d hne]
  exact div_le_div_of_nonneg_right hratio (by positivity)

/-- Normalized lower bound for the nontrivial Shor drift branch from an
explicit absolute phase-angle bound. This is the source-faithful interface used
by the later nearest-fraction and quotient-length estimates. -/
theorem lowerBound_le_norm_scaled_shorSourceJointDriftSum_of_angle_of_orbit_lt_phaseRegister
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t) (c : Fin (2 ^ t)) (d : Fin r) {A : ℝ}
    (hApos : 0 < A) (hApi : A ≤ Real.pi)
    (hangle :
      Real.pi *
          (((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) *
            |((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val|) ≤
        A)
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    ((((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) *
        (Real.sin A / A)) / (2 : ℝ) ^ t) ≤
      ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖ := by
  have hratio :=
    geometric_phase_norm_ratio_lower_bound_of_angle_le
      (θ := ((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val)
      (A := A)
      (m := ((2 ^ t - 1 - k.val) / r) + 1)
      hApos hApi hangle hne
  rw [norm_scaled_shorSourceJointDriftSum_eq_geometric_ratio_of_orbit_lt_phaseRegister
    hr hkq c d hne]
  exact div_le_div_of_nonneg_right hratio (by positivity)

/-- Normalized lower bound for the nontrivial Shor drift branch from an
explicit absolute phase-angle bound. This is the source-faithful interface used
by the later nearest-fraction and quotient-length estimates. -/
theorem lowerBound_le_norm_scaled_shorSourceJointDriftSum_of_angle
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t)
    (c : Fin (2 ^ t)) (k d : Fin r) {A : ℝ}
    (hApos : 0 < A) (hApi : A ≤ Real.pi)
    (hangle :
      Real.pi *
          (((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) *
            |((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val|) ≤
        A)
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    ((((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) *
        (Real.sin A / A)) / (2 : ℝ) ^ t) ≤
      ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖ := by
  exact
    lowerBound_le_norm_scaled_shorSourceJointDriftSum_of_angle_of_orbit_lt_phaseRegister
      (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)
      (shorSourceJointOrbit_lt_phaseRegister_of_large hlarge k)
      c d hApos hApi hangle hne

/-- Normalized lower bound for the nontrivial Shor drift branch from the
nearest-fraction scaled-error estimate. The resulting angle `A` is the
source-derived half window `π m r / (2q)`, with `q = 2^t` and `m` the quotient
length of the selected orbit. -/
theorem lowerBound_le_norm_scaled_shorSourceJointDriftSum_of_scaled_error_of_quotient_bounds
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t)
    (hbounds :
      (11 / 12 : ℝ) ≤
          (((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
            (2 : ℝ) ^ t ∧
        (((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
            (2 : ℝ) ^ t ≤ (13 / 12 : ℝ))
    (c : Fin (2 ^ t)) (d : Fin r)
    (hδ :
      |((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val| ≤
        (r : ℝ) / (2 * (2 : ℝ) ^ t))
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    let m : ℕ := ((2 ^ t - 1 - k.val) / r) + 1
    let A : ℝ := Real.pi * (((m : ℝ) * (r : ℝ)) / (2 * (2 : ℝ) ^ t))
    ((((m : ℝ) * (Real.sin A / A)) / (2 : ℝ) ^ t) ≤
      ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖) := by
  let m : ℕ := ((2 ^ t - 1 - k.val) / r) + 1
  let A : ℝ := Real.pi * (((m : ℝ) * (r : ℝ)) / (2 * (2 : ℝ) ^ t))
  have hq_pos : 0 < (2 : ℝ) ^ t := by
    positivity
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hbounds :
      (11 / 12 : ℝ) ≤ ((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t ∧
        ((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t ≤ (13 / 12 : ℝ) := by
    simpa [m] using hbounds
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hApi : A ≤ Real.pi := by
    have hx : ((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t ≤ (13 / 12 : ℝ) :=
      hbounds.2
    have hxhalf :
        ((m : ℝ) * (r : ℝ)) / (2 * (2 : ℝ) ^ t) ≤ (1 : ℝ) := by
      calc
        ((m : ℝ) * (r : ℝ)) / (2 * (2 : ℝ) ^ t) =
            (((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t) / 2 := by
          field_simp [hq_pos.ne']
        _ ≤ (13 / 12 : ℝ) / 2 :=
          div_le_div_of_nonneg_right hx (by norm_num)
        _ ≤ 1 := by norm_num
    dsimp [A]
    nlinarith [Real.pi_pos]
  have hangle :
      Real.pi * ((m : ℝ) *
          |((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val|) ≤ A := by
    have hmul :
        (m : ℝ) *
            |((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val| ≤
          (m : ℝ) * ((r : ℝ) / (2 * (2 : ℝ) ^ t)) := by
      exact mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg m)
    dsimp [A]
    calc
      Real.pi * ((m : ℝ) *
          |((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val|) ≤
        Real.pi * ((m : ℝ) * ((r : ℝ) / (2 * (2 : ℝ) ^ t))) :=
          mul_le_mul_of_nonneg_left hmul Real.pi_pos.le
      _ = Real.pi * ((m : ℝ) * (r : ℝ) / (2 * (2 : ℝ) ^ t)) := by
        field_simp [hq_pos.ne']
  simpa [m, A] using
    lowerBound_le_norm_scaled_shorSourceJointDriftSum_of_angle_of_orbit_lt_phaseRegister
      (t := t) (r := r) hr hkq c d
      (A := A) hApos hApi hangle hne

/-- Normalized lower bound for the nontrivial Shor drift branch from the
nearest-fraction scaled-error estimate. The resulting angle `A` is the
source-derived half window `π m r / (2q)`, with `q = 2^t` and `m` the quotient
length of the selected orbit. -/
theorem lowerBound_le_norm_scaled_shorSourceJointDriftSum_of_scaled_error
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t)
    (c : Fin (2 ^ t)) (k d : Fin r)
    (hδ :
      |((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val| ≤
        (r : ℝ) / (2 * (2 : ℝ) ^ t))
    (hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1) :
    let m : ℕ := ((2 ^ t - 1 - k.val) / r) + 1
    let A : ℝ := Real.pi * (((m : ℝ) * (r : ℝ)) / (2 * (2 : ℝ) ^ t))
    ((((m : ℝ) * (Real.sin A / A)) / (2 : ℝ) ^ t) ≤
      ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖) := by
  exact
    lowerBound_le_norm_scaled_shorSourceJointDriftSum_of_scaled_error_of_quotient_bounds
      (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)
      (shorSourceJointOrbit_lt_phaseRegister_of_large hlarge k)
      (by
        simpa using shorSourceJointQuotientLength_scaled_bounds hlarge k)
      c d hδ hne

/-- On the source-derived Shor angle window around `π/2`, sine is at least
`11/12`. -/
private theorem eleven_div_twelve_le_sin_of_mem_shor_window
    {A : ℝ}
    (hlo : (11 / 24 : ℝ) * Real.pi ≤ A)
    (hhi : A ≤ (13 / 24 : ℝ) * Real.pi) :
    (11 / 12 : ℝ) ≤ Real.sin A := by
  by_cases hle : A ≤ Real.pi / 2
  · have hA0 : 0 ≤ A := by
      nlinarith [Real.pi_pos]
    have hsin := Real.mul_le_sin hA0 hle
    have hlinear : (11 / 12 : ℝ) ≤ (2 / Real.pi) * A := by
      calc
        (11 / 12 : ℝ) = (2 / Real.pi) * ((11 / 24 : ℝ) * Real.pi) := by
          field_simp [Real.pi_pos.ne']
          norm_num
        _ ≤ (2 / Real.pi) * A := by
          gcongr
    exact le_trans hlinear hsin
  · let B : ℝ := Real.pi - A
    have hB0 : 0 ≤ B := by
      dsimp [B]
      nlinarith [hhi, Real.pi_pos]
    have hBle : B ≤ Real.pi / 2 := by
      dsimp [B]
      nlinarith
    have hBlo : (11 / 24 : ℝ) * Real.pi ≤ B := by
      dsimp [B]
      nlinarith [hhi]
    have hsin := Real.mul_le_sin hB0 hBle
    have hlinear : (11 / 12 : ℝ) ≤ (2 / Real.pi) * B := by
      calc
        (11 / 12 : ℝ) = (2 / Real.pi) * ((11 / 24 : ℝ) * Real.pi) := by
          field_simp [Real.pi_pos.ne']
          norm_num
        _ ≤ (2 / Real.pi) * B := by
          gcongr
    have hsinBA : Real.sin B = Real.sin A := by
      simp [B, Real.sin_pi_sub]
    rw [← hsinBA]
    exact le_trans hlinear hsin

/-- The Shor sine-window lower bound implies the source pointwise square
constant after scaling by the order. -/
private theorem one_div_three_order_sq_le_two_sin_div_pi_order_sq
    {r : ℕ} (hr : 0 < r) {A : ℝ}
    (hsin : (11 / 12 : ℝ) ≤ Real.sin A) :
    1 / (3 * (r : ℝ) ^ 2) ≤
      ((2 * Real.sin A) / (Real.pi * (r : ℝ))) ^ 2 := by
  have hrR_pos : 0 < (r : ℝ) := by
    exact_mod_cast hr
  have hpi_upper : Real.pi ≤ (63 / 20 : ℝ) := by
    linarith [Real.pi_lt_d2]
  have hnum_lower : (11 / 6 : ℝ) ≤ 2 * Real.sin A := by
    nlinarith
  have hfrac_lower : (110 / 189 : ℝ) ≤ (2 * Real.sin A) / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [hpi_upper, hnum_lower]
  have hfrac_nonneg : 0 ≤ (2 * Real.sin A) / Real.pi :=
    le_trans (by norm_num) hfrac_lower
  have hsq_frac :
      (1 / 3 : ℝ) ≤ ((2 * Real.sin A) / Real.pi) ^ 2 := by
    have hconst : (1 / 3 : ℝ) ≤ (110 / 189 : ℝ) ^ 2 := by
      norm_num
    have hpow :
        (110 / 189 : ℝ) ^ 2 ≤ ((2 * Real.sin A) / Real.pi) ^ 2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 110 / 189) hfrac_lower 2
    exact le_trans hconst hpow
  calc
    1 / (3 * (r : ℝ) ^ 2) = (1 / 3 : ℝ) / (r : ℝ) ^ 2 := by
      ring
    _ ≤ (((2 * Real.sin A) / Real.pi) ^ 2) / (r : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsq_frac (sq_nonneg _)
    _ = ((2 * Real.sin A) / (Real.pi * (r : ℝ))) ^ 2 := by
      field_simp [hrR_pos.ne', Real.pi_pos.ne']

/-- Source-faithful pointwise lower bound for a Shor drift sum selected by a
nearest-fraction scaled-error certificate and explicit quotient-length bounds.
This is the core proof route; large-register and finite residual wrappers only
provide the arithmetic premises. -/
theorem shorSourceJointDriftSum_scaled_normSq_lower_of_scaled_error_of_quotient_bounds
    {t r : ℕ} (hr : 0 < r) {k : Fin r}
    (hkq : k.val < 2 ^ t)
    (hbounds :
      (11 / 12 : ℝ) ≤
          (((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
            (2 : ℝ) ^ t ∧
        (((((2 ^ t - 1 - k.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
            (2 : ℝ) ^ t ≤ (13 / 12 : ℝ))
    (c : Fin (2 ^ t)) (d : Fin r)
    (hδ :
      |((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val| ≤
        (r : ℝ) / (2 * (2 : ℝ) ^ t)) :
    shorRecoverableStatePointwiseLowerBound r ≤
      ‖(((2 : ℝ) ^ t : ℂ))⁻¹ *
        shorSourceJointDriftSum t r c k d‖ ^ 2 := by
  let m : ℕ := ((2 ^ t - 1 - k.val) / r) + 1
  let A : ℝ := Real.pi * (((m : ℝ) * (r : ℝ)) / (2 * (2 : ℝ) ^ t))
  let normDrift : ℝ :=
    ‖(((2 : ℝ) ^ t : ℂ))⁻¹ *
      shorSourceJointDriftSum t r c k d‖
  have hrR_pos : 0 < (r : ℝ) := by
    exact_mod_cast hr
  have hq_pos : 0 < (2 : ℝ) ^ t := by
    positivity
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hmR_ne : (m : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hm_pos)
  have hbounds :
      (11 / 12 : ℝ) ≤ ((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t ∧
        ((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t ≤ (13 / 12 : ℝ) := by
    simpa [m] using hbounds
  have hAlo : (11 / 24 : ℝ) * Real.pi ≤ A := by
    have hxlo : (11 / 24 : ℝ) ≤
        (((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t) / 2 := by
      nlinarith [hbounds.1]
    dsimp [A]
    calc
      (11 / 24 : ℝ) * Real.pi =
          Real.pi * (11 / 24 : ℝ) := by ring
      _ ≤ Real.pi * ((((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t) / 2) :=
        mul_le_mul_of_nonneg_left hxlo Real.pi_pos.le
      _ = Real.pi * ((m : ℝ) * (r : ℝ) / (2 * (2 : ℝ) ^ t)) := by
        field_simp [hq_pos.ne']
  have hAhi : A ≤ (13 / 24 : ℝ) * Real.pi := by
    have hxhi :
        (((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t) / 2 ≤
          (13 / 24 : ℝ) := by
      nlinarith [hbounds.2]
    dsimp [A]
    calc
      Real.pi * ((m : ℝ) * (r : ℝ) / (2 * (2 : ℝ) ^ t)) =
          Real.pi * ((((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t) / 2) := by
        field_simp [hq_pos.ne']
      _ ≤ Real.pi * (13 / 24 : ℝ) :=
        mul_le_mul_of_nonneg_left hxhi Real.pi_pos.le
      _ = (13 / 24 : ℝ) * Real.pi := by ring
  have hsin : (11 / 12 : ℝ) ≤ Real.sin A :=
    eleven_div_twelve_le_sin_of_mem_shor_window hAlo hAhi
  have hsourceSquare :
      1 / (3 * (r : ℝ) ^ 2) ≤
        ((2 * Real.sin A) / (Real.pi * (r : ℝ))) ^ 2 :=
    one_div_three_order_sq_le_two_sin_div_pi_order_sq hr hsin
  by_cases hne :
      Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) ≠ 1
  · have hnormLower :
        (((m : ℝ) * (Real.sin A / A)) / (2 : ℝ) ^ t) ≤ normDrift := by
      simpa [m, A, normDrift] using
        lowerBound_le_norm_scaled_shorSourceJointDriftSum_of_scaled_error_of_quotient_bounds
          (t := t) (r := r) hr hkq hbounds c d hδ hne
    have hleftEq :
        (((m : ℝ) * (Real.sin A / A)) / (2 : ℝ) ^ t) =
          (2 * Real.sin A) / (Real.pi * (r : ℝ)) := by
      dsimp [A]
      field_simp [hq_pos.ne', Real.pi_pos.ne', hrR_pos.ne', hmR_ne]
    have hleftNonneg :
        0 ≤ (((m : ℝ) * (Real.sin A / A)) / (2 : ℝ) ^ t) := by
      rw [hleftEq]
      have hsin_nonneg : 0 ≤ Real.sin A := le_trans (by norm_num) hsin
      positivity
    have hsqToNorm :
        (((m : ℝ) * (Real.sin A / A)) / (2 : ℝ) ^ t) ^ 2 ≤
          normDrift ^ 2 :=
      pow_le_pow_left₀ hleftNonneg hnormLower 2
    calc
      shorRecoverableStatePointwiseLowerBound r =
          1 / (3 * (r : ℝ) ^ 2) := by
        rfl
      _ ≤ ((2 * Real.sin A) / (Real.pi * (r : ℝ))) ^ 2 := hsourceSquare
      _ = (((m : ℝ) * (Real.sin A / A)) / (2 : ℝ) ^ t) ^ 2 := by
        exact (congrArg (fun x : ℝ => x ^ 2) hleftEq).symm
      _ ≤ normDrift ^ 2 := hsqToNorm
  · have hbase :
        Complex.exp (2 * Real.pi *
          ((((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val : ℝ) : ℂ) *
            Complex.I) = 1 := not_ne_iff.mp hne
    have hnormEq : normDrift = (m : ℝ) / (2 : ℝ) ^ t := by
      dsimp [normDrift]
      change
        ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖ =
          (m : ℝ) / (2 : ℝ) ^ t
      rw [norm_scaled_shorSourceJointDriftSum_eq]
      rw [shorSourceJointDriftSum_eq_card_of_orbit_lt_phaseRegister_of_base_eq_one
        hr hkq c d hbase]
      rw [Complex.norm_natCast]
    have hmqLower : (11 / (12 * (r : ℝ)) : ℝ) ≤ (m : ℝ) / (2 : ℝ) ^ t := by
      calc
        (11 / (12 * (r : ℝ)) : ℝ) =
            (11 / 12 : ℝ) / (r : ℝ) := by ring
        _ ≤ (((m : ℝ) * (r : ℝ)) / (2 : ℝ) ^ t) / (r : ℝ) :=
          div_le_div_of_nonneg_right hbounds.1 hrR_pos.le
        _ = (m : ℝ) / (2 : ℝ) ^ t := by
          field_simp [hrR_pos.ne', hq_pos.ne']
    have hmqNonneg : 0 ≤ (m : ℝ) / (2 : ℝ) ^ t := by
      positivity
    have hconst :
        1 / (3 * (r : ℝ) ^ 2) ≤ (11 / (12 * (r : ℝ)) : ℝ) ^ 2 := by
      field_simp [hrR_pos.ne']
      norm_num
    have hpow :
        (11 / (12 * (r : ℝ)) : ℝ) ^ 2 ≤
          ((m : ℝ) / (2 : ℝ) ^ t) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hmqLower 2
    calc
      shorRecoverableStatePointwiseLowerBound r =
          1 / (3 * (r : ℝ) ^ 2) := by
        rfl
      _ ≤ (11 / (12 * (r : ℝ)) : ℝ) ^ 2 := hconst
      _ ≤ ((m : ℝ) / (2 : ℝ) ^ t) ^ 2 := hpow
      _ = normDrift ^ 2 := by rw [hnormEq]

/-- Source-faithful pointwise lower bound for a Shor drift sum selected by a
nearest-fraction scaled-error certificate. -/
theorem shorSourceJointDriftSum_scaled_normSq_lower_of_scaled_error
    {t r : ℕ} (hlarge : 12 * r ≤ 2 ^ t)
    (c : Fin (2 ^ t)) (k d : Fin r)
    (hδ :
      |((r : ℝ) * (c.val : ℝ)) / (2 : ℝ) ^ t - d.val| ≤
        (r : ℝ) / (2 * (2 : ℝ) ^ t)) :
    shorRecoverableStatePointwiseLowerBound r ≤
      ‖(((2 : ℝ) ^ t : ℂ))⁻¹ *
        shorSourceJointDriftSum t r c k d‖ ^ 2 := by
  exact
    shorSourceJointDriftSum_scaled_normSq_lower_of_scaled_error_of_quotient_bounds
      (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)
      (shorSourceJointOrbit_lt_phaseRegister_of_large hlarge k)
      (by
        simpa using shorSourceJointQuotientLength_scaled_bounds hlarge k)
      c d hδ

/-- Reindexed and drift-factored source joint amplitude. The remaining sum is
now written in terms of the scaled phase error for the target numerator `d`. -/
theorem shorSourceJointAmplitude_eq_orbit_phase_mul_quotient_drift_sum
    {t r : ℕ} (hr : 0 < r) (outcome : ShorSourceJointOutcome t r)
    (d : Fin r) :
    shorSourceJointAmplitude t r outcome =
      (((2 : ℝ) ^ t : ℂ))⁻¹ *
        (Complex.exp (2 * Real.pi *
            ((((outcome.2.val : ℝ) * (outcome.1.val : ℝ)) /
              (2 : ℝ) ^ t : ℝ)) * Complex.I) *
          shorSourceJointDriftSum t r outcome.1 outcome.2 d) := by
  rw [shorSourceJointAmplitude_eq_orbit_phase_mul_quotient_step_sum hr]
  congr 1
  congr 1
  unfold shorSourceJointDriftSum
  refine Finset.sum_congr rfl fun b _hb => ?_
  exact shorSourceJointQuotient_step_phase_eq_drift_phase outcome.1 d b

/-- Source-side joint probability obtained from the arithmetic-progression
amplitude. -/
def shorSourceJointProbability (t r : ℕ)
    (outcome : ShorSourceJointOutcome t r) : ℝ :=
  ‖shorSourceJointAmplitude t r outcome‖ ^ 2

/-- The source joint probability is the normalized squared norm of the
drift-indexed quotient sum; the orbit phase has unit norm. -/
theorem shorSourceJointProbability_eq_normSq_scaled_driftSum
    {t r : ℕ} (hr : 0 < r) (outcome : ShorSourceJointOutcome t r)
    (d : Fin r) :
    shorSourceJointProbability t r outcome =
      ‖(((2 : ℝ) ^ t : ℂ))⁻¹ *
        shorSourceJointDriftSum t r outcome.1 outcome.2 d‖ ^ 2 := by
  unfold shorSourceJointProbability
  rw [shorSourceJointAmplitude_eq_orbit_phase_mul_quotient_drift_sum hr outcome d]
  congr 1
  have hphase :
      ‖Complex.exp (2 * Real.pi *
        ((((outcome.2.val : ℝ) * (outcome.1.val : ℝ)) /
          (2 : ℝ) ^ t : ℝ)) * Complex.I)‖ = 1 := by
    simpa using
      Complex.norm_exp_ofReal_mul_I
        (2 * Real.pi *
          (((outcome.2.val : ℝ) * (outcome.1.val : ℝ)) / (2 : ℝ) ^ t))
  rw [norm_mul, norm_mul, hphase, one_mul, ← norm_mul]

/-- A lower bound for the normalized drift sum gives the corresponding
pointwise source joint probability lower bound. This isolates the remaining
finite geometric/sine estimate from the source-probability plumbing. -/
theorem shorSourceJointProbability_lowerBound_of_scaled_driftSum
    {t r : ℕ} (hr : 0 < r) {c : Fin (2 ^ t)} {k d : Fin r}
    (hbound :
      shorRecoverableStatePointwiseLowerBound r ≤
        ‖(((2 : ℝ) ^ t : ℂ))⁻¹ * shorSourceJointDriftSum t r c k d‖ ^ 2) :
    shorRecoverableStatePointwiseLowerBound r ≤
      shorSourceJointProbability t r (c, k) := by
  rw [shorSourceJointProbability_eq_normSq_scaled_driftSum hr (c, k) d]
  exact hbound

theorem shorSourceJointProbability_nonneg (t r : ℕ)
    (outcome : ShorSourceJointOutcome t r) :
    0 ≤ shorSourceJointProbability t r outcome := by
  unfold shorSourceJointProbability
  positivity

/-- Public-facing probability distribution for the source-joint order-finding
run used by the current endpoint. The implementation unfolds to Shor's source
distribution, while public endpoint theorems can talk about output-success mass
without exposing raw recoverable-event sums. -/
def orderFindingPublicOutcomeProbability (t r : ℕ) :
    ShorSourceJointOutcome t r → ℝ :=
  shorSourceJointProbability t r

theorem orderFindingPublicOutcomeProbability_nonneg (t r : ℕ)
    (outcome : ShorSourceJointOutcome t r) :
    0 ≤ orderFindingPublicOutcomeProbability t r outcome :=
  shorSourceJointProbability_nonneg t r outcome

/-- If the phase-event assignment is injective on coprime numerator indices,
then the joint recoverable source events have the source cardinality
`r * φ(r)`. -/
theorem card_shorSourceJointRecoverableEvents {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t))
    (hinj :
      Set.InjOn eventOf
        (↑(shorRecoverableFractionIndices r) : Set (Fin r))) :
    (shorSourceJointRecoverableEvents (t := t) (r := r) eventOf).card =
      shorRecoverableStateCount r := by
  unfold shorSourceJointRecoverableEvents
  rw [Finset.card_image_of_injOn ?_, card_shorRecoverableStateIndices]
  intro idx hidx idx' hidx' heq
  have hphase : eventOf idx.2 = eventOf idx'.2 := congrArg Prod.fst heq
  have horbit : idx.1 = idx'.1 := congrArg Prod.snd heq
  have hidx_frac : idx.2 ∈ shorRecoverableFractionIndices r := by
    simpa [shorRecoverableStateIndices] using hidx
  have hidx'_frac : idx'.2 ∈ shorRecoverableFractionIndices r := by
    simpa [shorRecoverableStateIndices] using hidx'
  exact Prod.ext horbit (hinj hidx_frac hidx'_frac hphase)

/-- An integer strictly above `-1/2` is nonnegative. -/
private theorem int_nonneg_of_neg_half_lt_cast {z : ℤ}
    (h : (-1 / 2 : ℝ) < z) :
    0 ≤ z := by
  by_contra hz
  have hzle : z ≤ -1 := by omega
  have hzleR : (z : ℝ) ≤ -1 := by exact_mod_cast hzle
  linarith

/-- For every coprime numerator label, there is a phase-register event within
Shor's nearest-fraction radius. The event is obtained by rounding
`2^t * d / r`; the hypotheses ensure that the rounded integer lies in the
phase-register range. -/
theorem exists_shorNearestFractionEvent {t r : ℕ}
    (d : Fin r) (hr : 0 < r)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t) :
    ∃ j : Fin (2 ^ t),
      |(j.val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
        1 / (2 * (2 : ℝ) ^ t) := by
  let q : ℝ := (2 : ℝ) ^ t
  let x : ℝ := (d.val : ℝ) * q / r
  let z : ℤ := round x
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hrR_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, q]
    positivity
  have hz_lower : (-1 / 2 : ℝ) < z := by
    have hsub : x - 1 / 2 < (z : ℝ) := by
      simpa [z] using sub_half_lt_round x
    linarith
  have hz_nonneg : 0 ≤ z := int_nonneg_of_neg_half_lt_cast hz_lower
  have hround : |x - (z : ℝ)| ≤ 1 / 2 := by
    simpa [z] using abs_sub_round x
  have hd_le_pred : (d.val : ℝ) ≤ (r : ℝ) - 1 := by
    have hd_succ_le : d.val + 1 ≤ r := Nat.succ_le_iff.mpr d.isLt
    have hd_succ_leR : (d.val : ℝ) + 1 ≤ r := by exact_mod_cast hd_succ_le
    linarith
  have hx_le : x ≤ ((r : ℝ) - 1) * q / r := by
    dsimp [x]
    gcongr
  have hq_div_gt_half : (1 / 2 : ℝ) < q / r := by
    have hr_ge_one : (1 : ℝ) ≤ r := by
      exact_mod_cast (Nat.succ_le_iff.mpr hr)
    have hhalf_lt_r : (1 / 2 : ℝ) < r := by linarith
    have hr_lt_q_div : (r : ℝ) < q / r := by
      rw [lt_div_iff₀ hrR_pos]
      simpa [q, pow_two] using hq
    exact lt_trans hhalf_lt_r hr_lt_q_div
  have hx_add_half_lt_q : x + 1 / 2 < q := by
    have hx_le' : x + 1 / 2 ≤ ((r : ℝ) - 1) * q / r + 1 / 2 := by
      linarith
    refine lt_of_le_of_lt hx_le' ?_
    calc
      ((r : ℝ) - 1) * q / r + 1 / 2 =
          q - q / r + 1 / 2 := by
        field_simp [hrR_pos.ne']
      _ < q := by linarith
  have hz_lt_q : (z : ℝ) < q := by
    exact lt_of_le_of_lt (by simpa [z] using round_le_add_half x) hx_add_half_lt_q
  have hz_lt_qNat : z < (2 ^ t : ℕ) := by
    have hz_lt_qNatR : (z : ℝ) < ((2 ^ t : ℕ) : ℝ) := by
      simpa [q] using hz_lt_q
    exact_mod_cast hz_lt_qNatR
  let j : Fin (2 ^ t) :=
    ⟨z.toNat, (Int.toNat_lt_of_ne_zero (by positivity : 2 ^ t ≠ 0)).mpr hz_lt_qNat⟩
  refine ⟨j, ?_⟩
  have hz_toNat_cast : (z.toNat : ℝ) = z := by
    exact_mod_cast Int.toNat_of_nonneg hz_nonneg
  have hround' : |(z : ℝ) - x| ≤ 1 / 2 := by
    simpa [abs_sub_comm] using hround
  calc
    |(j.val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| =
        |((z : ℝ) - x) / q| := by
      dsimp [j, x, q]
      rw [hz_toNat_cast]
      congr 1
      field_simp [hq_pos.ne', hrR_pos.ne']
    _ = |(z : ℝ) - x| / q := by
      rw [abs_div, abs_of_pos hq_pos]
    _ ≤ (1 / 2) / q := by
      exact div_le_div_of_nonneg_right hround' hq_pos.le
    _ = 1 / (2 * q) := by
      field_simp [hq_pos.ne']

/-- The rounded nearest-fraction phase event selected by
`exists_shorNearestFractionEvent`. -/
noncomputable def shorNearestFractionEvent {t r : ℕ}
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (d : Fin r) : Fin (2 ^ t) :=
  Classical.choose (exists_shorNearestFractionEvent d hr hq)

/-- The selected rounded phase event satisfies Shor's nearest-fraction radius. -/
theorem shorNearestFractionEvent_nearestFraction {t r : ℕ}
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (d : Fin r) :
    |((shorNearestFractionEvent (t := t) (r := r) hr hq d).val : ℝ) /
        (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
      1 / (2 * (2 : ℝ) ^ t) :=
  Classical.choose_spec (exists_shorNearestFractionEvent d hr hq)

/-- The selected rounded event is already a good phase-register outcome for
continued-fraction recovery. -/
private theorem shorNearestFractionEvent_isGoodPhaseRegisterOutcome {t r : ℕ}
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (d : Fin r) :
    IsGoodPhaseRegisterOutcome t d.val r
      (shorNearestFractionEvent (t := t) (r := r) hr hq d) :=
  shorNearestFraction_isGoodPhaseRegisterOutcome hr hq
    (shorNearestFractionEvent_nearestFraction hr hq d)

/-- Scaled nearest-fraction error for the rounded phase event. This is the
form used by the source-level geometric-sum lower-bound pass. -/
theorem shorNearestFractionEvent_scaled_error_le {t r : ℕ}
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (d : Fin r) :
    |(r : ℝ) *
        ((shorNearestFractionEvent (t := t) (r := r) hr hq d).val : ℝ) /
          (2 : ℝ) ^ t - d.val| ≤
      (r : ℝ) / (2 * (2 : ℝ) ^ t) := by
  let j : ℝ :=
    ((shorNearestFractionEvent (t := t) (r := r) hr hq d).val : ℝ)
  let q : ℝ := (2 : ℝ) ^ t
  have hrR_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnear :
      |j / q - (d.val : ℝ) / r| ≤ 1 / (2 * q) := by
    simpa [j, q] using
      shorNearestFractionEvent_nearestFraction (t := t) (r := r) hr hq d
  have htarget :
      |(r : ℝ) * j / q - d.val| =
        (r : ℝ) * |j / q - (d.val : ℝ) / r| := by
    calc
      |(r : ℝ) * j / q - d.val| =
          |(r : ℝ) * (j / q - (d.val : ℝ) / r)| := by
        congr 1
        field_simp [hrR_pos.ne']
      _ = (r : ℝ) * |j / q - (d.val : ℝ) / r| := by
        rw [abs_mul, abs_of_pos hrR_pos]
  calc
    |(r : ℝ) * j / q - d.val| =
        (r : ℝ) * |j / q - (d.val : ℝ) / r| := htarget
    _ ≤ (r : ℝ) * (1 / (2 * q)) :=
      mul_le_mul_of_nonneg_left hnear hrR_pos.le
    _ = (r : ℝ) / (2 * q) := by
      ring

/-- Rounded nearest-fraction pointwise source bound reduced to the drift-sum
lower-bound obligation for each recoverable state. -/
theorem shorSourceJointProbability_roundedNearestFractionEvent_pointwise_of_driftSum
    {t r : ℕ} (hr : 0 < r)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hdrift :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          ‖(((2 : ℝ) ^ t : ℂ))⁻¹ *
            shorSourceJointDriftSum t r
              (shorNearestFractionEvent hr hq idx.2) idx.1 idx.2‖ ^ 2) :
    ∀ idx, idx ∈ shorRecoverableStateIndices r →
      shorRecoverableStatePointwiseLowerBound r ≤
        shorSourceJointProbability t r
          (shorNearestFractionEvent hr hq idx.2, idx.1) := by
  intro idx hidx
  exact shorSourceJointProbability_lowerBound_of_scaled_driftSum hr
    (hdrift idx hidx)

/-- Rounded nearest-fraction pointwise source bound, with the drift-sum
lower-bound obligation discharged by the finite geometric/sine estimate. -/
theorem shorSourceJointProbability_roundedNearestFractionEvent_pointwise
    {t r : ℕ} (hr : 0 < r)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t) :
    ∀ idx, idx ∈ shorRecoverableStateIndices r →
      shorRecoverableStatePointwiseLowerBound r ≤
        shorSourceJointProbability t r
          (shorNearestFractionEvent hr hq idx.2, idx.1) := by
  intro idx _hidx
  exact shorSourceJointProbability_lowerBound_of_scaled_driftSum hr
    (shorSourceJointDriftSum_scaled_normSq_lower_of_scaled_error
      hlarge (shorNearestFractionEvent hr hq idx.2) idx.1 idx.2
      (shorNearestFractionEvent_scaled_error_le hr hq idx.2))

/-- The scaled-error premise implies that every orbit representative is within
the phase-register range. This is the finite bound needed by the quotient-bound
version of Shor's source probability estimate [Sho95, source.tex:1183-1185]. -/
theorem shorSourceJointOrbit_lt_phaseRegister_of_scaledError
    {t r : ℕ} (hr : 0 < r)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t) (k : Fin r) :
    k.val < 2 ^ t := by
  have hq_nat : r ^ 2 < 2 ^ t := by
    exact_mod_cast hq
  have hr_le_sq : r ≤ r ^ 2 := by
    nlinarith [Nat.succ_le_iff.mpr hr]
  exact lt_trans k.isLt (lt_of_le_of_lt hr_le_sq hq_nat)

/-- Rounded nearest-fraction pointwise source bound, with the drift-sum
lower-bound obligation discharged by explicit quotient-length bounds. This is
the reusable interface for finite residual cases where the large-register route
does not apply but Shor's geometric/sine estimate is still verified directly
[Sho95, source.tex:1183-1185]. -/
theorem shorSourceJointProbability_roundedNearestFractionEvent_pointwise_of_quotient_bounds
    {t r : ℕ} (hr : 0 < r)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hbounds :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        (11 / 12 : ℝ) ≤
            (((((2 ^ t - 1 - idx.1.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
              (2 : ℝ) ^ t ∧
          (((((2 ^ t - 1 - idx.1.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
              (2 : ℝ) ^ t ≤ (13 / 12 : ℝ)) :
    ∀ idx, idx ∈ shorRecoverableStateIndices r →
      shorRecoverableStatePointwiseLowerBound r ≤
        shorSourceJointProbability t r
          (shorNearestFractionEvent hr hq idx.2, idx.1) := by
  intro idx hidx
  exact shorSourceJointProbability_lowerBound_of_scaled_driftSum hr
    (shorSourceJointDriftSum_scaled_normSq_lower_of_scaled_error_of_quotient_bounds
      hr (shorSourceJointOrbit_lt_phaseRegister_of_scaledError hr hq idx.1)
      (hbounds idx hidx)
      (shorNearestFractionEvent hr hq idx.2) idx.2
      (shorNearestFractionEvent_scaled_error_le hr hq idx.2))

/-- A source-level nearest-fraction estimate for every recoverable numerator
supplies the Lean good-outcome predicate used by continued fractions. -/
theorem shorRecoverableFractionEvents_good_of_nearestFraction {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t)) (hr : 0 < r)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        |((eventOf d).val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
          1 / (2 * (2 : ℝ) ^ t)) :
    ∀ d, d ∈ shorRecoverableFractionIndices r →
      IsGoodPhaseRegisterOutcome t d.val r (eventOf d) := by
  intro d hd
  exact shorNearestFraction_isGoodPhaseRegisterOutcome hr hq (hnear d hd)

/-- Nearest-fraction events are injective on the recoverable coprime numerators.
If two numerators had the same phase event, both reduced fractions would be
within `1/(2q)` of the same dyadic point, forcing their real distance below
`1/r`; integer discreteness then gives equal numerator labels. -/
theorem shorRecoverableFractionEvents_injOn_of_nearestFraction {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t)) (hr : 0 < r)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        |((eventOf d).val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
          1 / (2 * (2 : ℝ) ^ t)) :
    Set.InjOn eventOf
      (↑(shorRecoverableFractionIndices r) : Set (Fin r)) := by
  intro d hd e he hevent
  apply Fin.ext
  apply RationalApproximation.nat_eq_of_abs_cast_sub_lt_one
  let q : ℝ := (2 : ℝ) ^ t
  let c : ℝ := ((eventOf d).val : ℝ)
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hrRpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnear_d : |c / q - (d.val : ℝ) / r| ≤ 1 / (2 * q) := by
    simpa [c, q] using hnear d hd
  have hnear_e : |c / q - (e.val : ℝ) / r| ≤ 1 / (2 * q) := by
    have h := hnear e he
    rw [← hevent] at h
    simpa [c, q] using h
  have hde_div : |(d.val : ℝ) / r - (e.val : ℝ) / r| ≤ 1 / q := by
    apply abs_sub_le_iff.mpr
    have hd_bounds := abs_sub_le_iff.mp hnear_d
    have he_bounds := abs_sub_le_iff.mp hnear_e
    have htwo : 1 / (2 * q) + 1 / (2 * q) = 1 / q := by
      field_simp [hqpos.ne']
      ring
    constructor
    · calc
        (d.val : ℝ) / r - (e.val : ℝ) / r =
            ((d.val : ℝ) / r - c / q) + (c / q - (e.val : ℝ) / r) := by ring
        _ ≤ 1 / (2 * q) + 1 / (2 * q) := by
          exact add_le_add hd_bounds.2 he_bounds.1
        _ = 1 / q := htwo
    · calc
        (e.val : ℝ) / r - (d.val : ℝ) / r =
            ((e.val : ℝ) / r - c / q) + (c / q - (d.val : ℝ) / r) := by ring
        _ ≤ 1 / (2 * q) + 1 / (2 * q) := by
          exact add_le_add he_bounds.2 hd_bounds.1
        _ = 1 / q := htwo
  have hq_gt_r : (r : ℝ) < q := by
    have hr_ge_one : (1 : ℝ) ≤ r := by
      exact_mod_cast (Nat.succ_le_iff.mpr hr)
    have hsq_ge : (r : ℝ) ≤ (r : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hr_ge_one (by positivity : 0 ≤ (r : ℝ))
      simpa [pow_two] using hmul
    exact lt_of_le_of_lt hsq_ge hq
  have hfrac_lt :
      |(d.val : ℝ) / r - (e.val : ℝ) / r| < 1 / (r : ℝ) :=
    lt_of_le_of_lt hde_div (one_div_lt_one_div_of_lt hrRpos hq_gt_r)
  have hscale :
      |((d.val : ℝ) - (e.val : ℝ))| =
        (r : ℝ) * |(d.val : ℝ) / r - (e.val : ℝ) / r| := by
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    calc
      |((d.val : ℝ) - (e.val : ℝ))| =
          |(r : ℝ) * (((d.val : ℝ) / r - (e.val : ℝ) / r))| := by
        congr 1
        field_simp [hrR]
      _ = |(r : ℝ)| * |(d.val : ℝ) / r - (e.val : ℝ) / r| := by
        rw [abs_mul]
      _ = (r : ℝ) * |(d.val : ℝ) / r - (e.val : ℝ) / r| := by
        rw [abs_of_nonneg]
        positivity
  calc
    |((d.val : ℝ) - (e.val : ℝ))| =
        (r : ℝ) * |(d.val : ℝ) / r - (e.val : ℝ) / r| := hscale
    _ < (r : ℝ) * (1 / (r : ℝ)) := by
      exact mul_lt_mul_of_pos_left hfrac_lt hrRpos
    _ = 1 := by
      field_simp [hrRpos.ne']

/-- Nearest-fraction events have the full source recoverable-state cardinality
once paired with all orbit coordinates. -/
private theorem card_shorSourceJointRecoverableEvents_of_nearestFraction {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t)) (hr : 0 < r)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        |((eventOf d).val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
          1 / (2 * (2 : ℝ) ^ t)) :
    (shorSourceJointRecoverableEvents (t := t) (r := r) eventOf).card =
      shorRecoverableStateCount r :=
  card_shorSourceJointRecoverableEvents eventOf
    (shorRecoverableFractionEvents_injOn_of_nearestFraction eventOf hr hq hnear)

/-- Pointwise source-event bounds imply the one-numerator joint marginal lower
bound, independently of the later joint-to-phase marginal comparison. -/
private theorem shorSingleNumeratorSuccessLowerBound_le_sourceJointMarginal_of_pointwise
    {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t))
    (prob : ShorSourceJointOutcome t r → ℝ)
    (d : Fin r) (hd : d ∈ shorRecoverableFractionIndices r)
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          prob (eventOf idx.2, idx.1)) :
    shorSingleNumeratorSuccessLowerBound r ≤
      ∑ k : Fin r, prob (eventOf d, k) := by
  calc
    shorSingleNumeratorSuccessLowerBound r =
        ∑ _k : Fin r, shorRecoverableStatePointwiseLowerBound r := by
      rw [shorSingleNumeratorSuccessLowerBound, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ k : Fin r, prob (eventOf d, k) := by
      refine Finset.sum_le_sum fun k _hk => ?_
      exact hpointwise (k, d) (by
        simp [shorRecoverableStateIndices, hd])

/-- Source-indexed certificate for Shor's joint recoverable events. The
analytic geometric-sum pass must instantiate `eventOf`, prove the assignment is
injective on coprime numerators, and prove the pointwise probability lower
bound for the joint distribution. -/
structure ShorSourceJointEventMapCertificate (t r : ℕ) where
  /-- Map from a recoverable output event to its source sample event. -/
  eventOf : Fin r → Fin (2 ^ t)
  injOnRecoverableFractions :
    Set.InjOn eventOf
      (↑(shorRecoverableFractionIndices r) : Set (Fin r))
  /-- Probability mass function on source samples. -/
  prob : ShorSourceJointOutcome t r → ℝ
  good :
    ∀ d, d ∈ shorRecoverableFractionIndices r →
      IsGoodPhaseRegisterOutcome t d.val r (eventOf d)
  pointwise :
    ∀ idx, idx ∈ shorRecoverableStateIndices r →
      shorRecoverableStatePointwiseLowerBound r ≤
        prob (eventOf idx.2, idx.1)
  nonneg_outside :
    ∀ outcome,
      outcome ∉ shorSourceJointRecoverableEvents (t := t) (r := r) eventOf →
        0 ≤ prob outcome

namespace ShorSourceJointEventMapCertificate

/-- Build the joint source-event certificate from nearest-fraction events and
the remaining source probability obligations. -/
def ofNearestFractionEvents {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t))
    (hinj :
      Set.InjOn eventOf
        (↑(shorRecoverableFractionIndices r) : Set (Fin r)))
    (prob : ShorSourceJointOutcome t r → ℝ)
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        |((eventOf d).val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
          1 / (2 * (2 : ℝ) ^ t))
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          prob (eventOf idx.2, idx.1))
    (hnonneg_outside :
      ∀ outcome,
        outcome ∉ shorSourceJointRecoverableEvents (t := t) (r := r) eventOf →
          0 ≤ prob outcome) :
    ShorSourceJointEventMapCertificate t r where
  eventOf := eventOf
  injOnRecoverableFractions := hinj
  prob := prob
  good := shorRecoverableFractionEvents_good_of_nearestFraction
    eventOf hr hq hnear
  pointwise := hpointwise
  nonneg_outside := hnonneg_outside

/-- Build the joint source-event certificate from nearest-fraction events,
deriving injectivity of the phase-event assignment from the same nearest
fraction estimates. -/
def ofNearestFractionEventsInferInjectivity {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t))
    (prob : ShorSourceJointOutcome t r → ℝ)
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        |((eventOf d).val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
          1 / (2 * (2 : ℝ) ^ t))
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          prob (eventOf idx.2, idx.1))
    (hnonneg_outside :
      ∀ outcome,
        outcome ∉ shorSourceJointRecoverableEvents (t := t) (r := r) eventOf →
          0 ≤ prob outcome) :
    ShorSourceJointEventMapCertificate t r :=
  ofNearestFractionEvents eventOf
    (shorRecoverableFractionEvents_injOn_of_nearestFraction eventOf hr hq hnear)
    prob hr hq hnear hpointwise hnonneg_outside

/-- Build the joint source-event certificate using the rounded nearest-fraction
phase event. The remaining source probability obligations are the pointwise
lower bound and nonnegativity away from the recoverable event set. -/
def ofRoundedNearestFractionEvents {t r : ℕ}
    (prob : ShorSourceJointOutcome t r → ℝ)
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          prob (shorNearestFractionEvent hr hq idx.2, idx.1))
    (hnonneg_outside :
      ∀ outcome,
        outcome ∉
            shorSourceJointRecoverableEvents
              (t := t) (r := r) (shorNearestFractionEvent hr hq) →
          0 ≤ prob outcome) :
    ShorSourceJointEventMapCertificate t r :=
  ofNearestFractionEventsInferInjectivity
    (shorNearestFractionEvent hr hq) prob hr hq
    (fun d _hd => shorNearestFractionEvent_nearestFraction hr hq d)
    hpointwise hnonneg_outside

/-- Build the joint source-event certificate using the concrete Shor
arithmetic-progression probability shape. The analytic lower-bound proof is
still supplied as the `hpointwise` premise. -/
def ofSourceJointProbability {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t))
    (hinj :
      Set.InjOn eventOf
        (↑(shorRecoverableFractionIndices r) : Set (Fin r)))
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        |((eventOf d).val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
          1 / (2 * (2 : ℝ) ^ t))
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          shorSourceJointProbability t r (eventOf idx.2, idx.1)) :
    ShorSourceJointEventMapCertificate t r where
  eventOf := eventOf
  injOnRecoverableFractions := hinj
  prob := shorSourceJointProbability t r
  good := shorRecoverableFractionEvents_good_of_nearestFraction
    eventOf hr hq hnear
  pointwise := hpointwise
  nonneg_outside := fun outcome _ =>
    shorSourceJointProbability_nonneg t r outcome

/-- Build the concrete-source joint event certificate, deriving injectivity of
the phase-event assignment from the nearest-fraction estimates. The analytic
pointwise probability lower bound remains an explicit premise. -/
def ofSourceJointProbabilityInferInjectivity {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t))
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        |((eventOf d).val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
          1 / (2 * (2 : ℝ) ^ t))
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          shorSourceJointProbability t r (eventOf idx.2, idx.1)) :
    ShorSourceJointEventMapCertificate t r :=
  ofSourceJointProbability eventOf
    (shorRecoverableFractionEvents_injOn_of_nearestFraction eventOf hr hq hnear)
    hr hq hnear hpointwise

/-- Build the concrete-source joint event certificate using the rounded
nearest-fraction event. The analytic pointwise probability lower bound remains
an explicit premise. -/
def ofSourceJointProbabilityRoundedNearestFractionEvents {t r : ℕ}
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          shorSourceJointProbability t r
            (shorNearestFractionEvent hr hq idx.2, idx.1)) :
    ShorSourceJointEventMapCertificate t r :=
  ofSourceJointProbabilityInferInjectivity
    (shorNearestFractionEvent hr hq) hr hq
    (fun d _hd => shorNearestFractionEvent_nearestFraction hr hq d)
    hpointwise

/-- Build the rounded concrete-source joint event certificate from the
drift-sum lower-bound obligation. This is the last plumbing layer before the
finite geometric/sine estimate. -/
def ofSourceJointProbabilityRoundedNearestFractionEventsOfDriftSum
    {t r : ℕ} (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hdrift :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          ‖(((2 : ℝ) ^ t : ℂ))⁻¹ *
            shorSourceJointDriftSum t r
              (shorNearestFractionEvent hr hq idx.2) idx.1 idx.2‖ ^ 2) :
    ShorSourceJointEventMapCertificate t r :=
  ofSourceJointProbabilityRoundedNearestFractionEvents hr hq
    (shorSourceJointProbability_roundedNearestFractionEvent_pointwise_of_driftSum
      hr hq hdrift)

/-- Build the rounded concrete-source joint event certificate directly from the
finite geometric/sine estimate. -/
def ofSourceJointProbabilityRoundedNearestFractionEventsOfScaledError
    {t r : ℕ} (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t) :
    ShorSourceJointEventMapCertificate t r :=
  ofSourceJointProbabilityRoundedNearestFractionEvents hr hq
    (shorSourceJointProbability_roundedNearestFractionEvent_pointwise
      hr hq hlarge)

/-- Build the rounded concrete-source joint event certificate from explicit
quotient-length bounds. This is the certificate boundary used for finite
small-modulus residual cases of the restored Shor register window
[Sho95, source.tex:1183-1185]. -/
def ofSourceJointProbabilityRoundedNearestFractionEventsOfQuotientBounds
    {t r : ℕ} (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hbounds :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        (11 / 12 : ℝ) ≤
            (((((2 ^ t - 1 - idx.1.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
              (2 : ℝ) ^ t ∧
          (((((2 ^ t - 1 - idx.1.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
              (2 : ℝ) ^ t ≤ (13 / 12 : ℝ)) :
    ShorSourceJointEventMapCertificate t r :=
  ofSourceJointProbabilityRoundedNearestFractionEvents hr hq
    (shorSourceJointProbability_roundedNearestFractionEvent_pointwise_of_quotient_bounds
      hr hq hbounds)

/-- The source-indexed joint event certificate gives the aggregate Shor
order-recovery lower bound over the certified recoverable-event mass. -/
theorem successLowerBound_le_recoverableMass {t r : ℕ}
    (cert : ShorSourceJointEventMapCertificate t r) (hr : 0 < r) :
    shorOrderRecoverySuccessLowerBound r ≤
      (shorSourceJointRecoverableEvents (t := t) (r := r) cert.eventOf).sum
        cert.prob := by
  calc
    shorOrderRecoverySuccessLowerBound r =
        (shorRecoverableStateCount r : ℝ) *
          shorRecoverableStatePointwiseLowerBound r := by
      exact (shorRecoverableStateCount_mul_pointwiseLowerBound_eq_successLowerBound
        (r := r) hr).symm
    _ =
        ((shorSourceJointRecoverableEvents (t := t) (r := r) cert.eventOf).card : ℝ) *
          shorRecoverableStatePointwiseLowerBound r := by
      rw [card_shorSourceJointRecoverableEvents cert.eventOf
        cert.injOnRecoverableFractions]
    _ =
        (shorSourceJointRecoverableEvents (t := t) (r := r) cert.eventOf).sum
          fun _outcome => shorRecoverableStatePointwiseLowerBound r := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤
        (shorSourceJointRecoverableEvents (t := t) (r := r) cert.eventOf).sum
          cert.prob := by
      refine Finset.sum_le_sum fun outcome houtcome => ?_
      rcases Finset.mem_image.mp houtcome with ⟨idx, hidx, rfl⟩
      exact cert.pointwise idx hidx

/-- Corollary of the recoverable-event mass theorem: when probabilities are
nonnegative away from the certified recoverable events, the same lower bound is
below the total joint mass. -/
theorem successLowerBound_le_totalMass {t r : ℕ}
    (cert : ShorSourceJointEventMapCertificate t r) (hr : 0 < r) :
    shorOrderRecoverySuccessLowerBound r ≤
      ∑ outcome : ShorSourceJointOutcome t r, cert.prob outcome := by
  refine le_trans (cert.successLowerBound_le_recoverableMass hr) ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (by intro outcome _; simp) ?_
  intro outcome _ houtcome
  exact cert.nonneg_outside outcome houtcome

end ShorSourceJointEventMapCertificate

/-- Certificate-shaped bridge from the measurement distribution to classical
denominator recovery. A later analytic pass can instantiate
`successLowerBound` with the source-specific lower bound, while this theorem
keeps the proof chain from good phase outcomes to continued-fraction recovery
explicit. -/
structure GeneralOrderRunCertificate (t s r : ℕ) where
  /-- A measured phase-register sample. -/
  sample : Fin (2 ^ t)
  /-- The sample lies within the continued-fraction recovery radius. -/
  good : IsGoodPhaseRegisterOutcome t s r sample
  /-- The sampled numerator is coprime to the true order. -/
  coprime : Nat.Coprime s r
  /-- Source-backed lower bound for the good-outcome probability mass. -/
  successLowerBound : ℝ
  /-- The source-backed lower bound is below the formal good-outcome mass. -/
  successLowerBound_le_goodMass :
    successLowerBound ≤ goodPhaseRegisterOutcomeMass t s r

namespace GeneralOrderRunCertificate

/-- Continued-fraction denominator recovery from the certified good sample. -/
theorem denominatorRecovery {t s r : ℕ}
    (cert : GeneralOrderRunCertificate t s r) (hr : 0 < r) :
    ∃ n,
      (s : ℚ) / (r : ℚ) =
        (((cert.sample.val : ℝ) / (2 : ℝ) ^ t).convergent n) ∧
      ((((cert.sample.val : ℝ) / (2 : ℝ) ^ t).convergent n).den = r) :=
  goodPhaseRegisterOutcome_denominatorRecovery hr cert.coprime cert.good

end GeneralOrderRunCertificate

/-- Source-to-phase marginal certificate for Shor's joint order-recovery
events. This is the boundary between the source-level joint distribution over
phase and orbit coordinates, and the formal fixed-eigenphase good-outcome mass
used by the continued-fraction denominator-recovery theorem. -/
structure ShorSourcePhaseMassCertificate (t r : ℕ)
    extends ShorSourceJointEventMapCertificate t r where
  marginal_le_goodMass :
    ∀ d, d ∈ shorRecoverableFractionIndices r →
      (∑ k : Fin r, prob (eventOf d, k)) ≤
        goodPhaseRegisterOutcomeMass t d.val r

namespace ShorSourcePhaseMassCertificate

/-- Build the phase-mass certificate using the concrete Shor source joint
probability shape. Pointwise lower bounds and the joint-to-phase marginal
comparison remain explicit analytic obligations. -/
def ofSourceJointProbability {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t))
    (hinj :
      Set.InjOn eventOf
        (↑(shorRecoverableFractionIndices r) : Set (Fin r)))
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        |((eventOf d).val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
          1 / (2 * (2 : ℝ) ^ t))
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          shorSourceJointProbability t r (eventOf idx.2, idx.1))
    (hmarginal :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        (∑ k : Fin r, shorSourceJointProbability t r (eventOf d, k)) ≤
          goodPhaseRegisterOutcomeMass t d.val r) :
    ShorSourcePhaseMassCertificate t r where
  eventOf := eventOf
  injOnRecoverableFractions := hinj
  prob := shorSourceJointProbability t r
  good := shorRecoverableFractionEvents_good_of_nearestFraction
    eventOf hr hq hnear
  pointwise := hpointwise
  nonneg_outside := fun outcome _ =>
    shorSourceJointProbability_nonneg t r outcome
  marginal_le_goodMass := hmarginal

/-- Build the phase-mass certificate using the concrete Shor source joint
probability shape, deriving injectivity of the phase-event assignment from the
nearest-fraction estimates. Pointwise lower bounds and the joint-to-phase
marginal comparison remain explicit analytic obligations. -/
def ofSourceJointProbabilityInferInjectivity {t r : ℕ}
    (eventOf : Fin r → Fin (2 ^ t))
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hnear :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        |((eventOf d).val : ℝ) / (2 : ℝ) ^ t - (d.val : ℝ) / r| ≤
          1 / (2 * (2 : ℝ) ^ t))
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          shorSourceJointProbability t r (eventOf idx.2, idx.1))
    (hmarginal :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        (∑ k : Fin r, shorSourceJointProbability t r (eventOf d, k)) ≤
          goodPhaseRegisterOutcomeMass t d.val r) :
    ShorSourcePhaseMassCertificate t r :=
  ofSourceJointProbability eventOf
    (shorRecoverableFractionEvents_injOn_of_nearestFraction eventOf hr hq hnear)
    hr hq hnear hpointwise hmarginal

/-- Build the phase-mass certificate using the rounded nearest-fraction event
and the concrete Shor source joint probability shape. The pointwise lower bound
and joint-to-phase marginal comparison remain explicit analytic obligations. -/
def ofSourceJointProbabilityRoundedNearestFractionEvents {t r : ℕ}
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hpointwise :
      ∀ idx, idx ∈ shorRecoverableStateIndices r →
        shorRecoverableStatePointwiseLowerBound r ≤
          shorSourceJointProbability t r
            (shorNearestFractionEvent hr hq idx.2, idx.1))
    (hmarginal :
      ∀ d, d ∈ shorRecoverableFractionIndices r →
        (∑ k : Fin r,
          shorSourceJointProbability t r (shorNearestFractionEvent hr hq d, k)) ≤
          goodPhaseRegisterOutcomeMass t d.val r) :
    ShorSourcePhaseMassCertificate t r :=
  ofSourceJointProbabilityInferInjectivity
    (shorNearestFractionEvent hr hq) hr hq
    (fun d _hd => shorNearestFractionEvent_nearestFraction hr hq d)
    hpointwise hmarginal

/-- Summing the pointwise joint lower bound over all orbit coordinates for one
recoverable numerator gives a lower bound on that numerator's formal
good-outcome mass, provided the joint distribution has the certified marginal
comparison. -/
theorem singleNumeratorSuccessLowerBound_le_goodMass {t r : ℕ}
    (cert : ShorSourcePhaseMassCertificate t r)
    (d : Fin r) (hd : d ∈ shorRecoverableFractionIndices r) :
    shorSingleNumeratorSuccessLowerBound r ≤
      goodPhaseRegisterOutcomeMass t d.val r := by
  calc
    shorSingleNumeratorSuccessLowerBound r =
        ∑ _k : Fin r, shorRecoverableStatePointwiseLowerBound r := by
      rw [shorSingleNumeratorSuccessLowerBound, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ k : Fin r, cert.prob (cert.eventOf d, k) := by
      refine Finset.sum_le_sum fun k _hk => ?_
      exact cert.pointwise (k, d) (by
        simp [shorRecoverableStateIndices, hd])
    _ ≤ goodPhaseRegisterOutcomeMass t d.val r :=
      cert.marginal_le_goodMass d hd

/-- Summing the certified per-numerator phase masses gives Shor's aggregate
order-recovery success lower bound. -/
theorem orderRecoverySuccessLowerBound_le_goodMassSum {t r : ℕ}
    (cert : ShorSourcePhaseMassCertificate t r) (hr : 0 < r) :
    shorOrderRecoverySuccessLowerBound r ≤
      (shorRecoverableFractionIndices r).sum
        (fun d => goodPhaseRegisterOutcomeMass t d.val r) := by
  calc
    shorOrderRecoverySuccessLowerBound r =
        ((shorRecoverableFractionIndices r).card : ℝ) *
          shorSingleNumeratorSuccessLowerBound r := by
      exact
        (recoverableFractionCount_mul_singleSuccess_eq_orderRecovery
          (r := r) hr).symm
    _ = (shorRecoverableFractionIndices r).sum
        (fun _d => shorSingleNumeratorSuccessLowerBound r) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (shorRecoverableFractionIndices r).sum
        (fun d => goodPhaseRegisterOutcomeMass t d.val r) := by
      exact Finset.sum_le_sum fun d hd =>
        cert.singleNumeratorSuccessLowerBound_le_goodMass d hd

/-- Convert a source marginal certificate for one coprime numerator into the
fixed-eigenphase run certificate consumed by the general-order integration
theorem. -/
def toGeneralOrderRunCertificate {t r : ℕ}
    (cert : ShorSourcePhaseMassCertificate t r)
    (d : Fin r) (hd : d ∈ shorRecoverableFractionIndices r) :
    GeneralOrderRunCertificate t d.val r where
  sample := cert.eventOf d
  good := cert.good d hd
  coprime := by
    have h : r.Coprime d.val := by
      simpa [shorRecoverableFractionIndices] using hd
    simpa [Nat.coprime_comm] using h
  successLowerBound := shorSingleNumeratorSuccessLowerBound r
  successLowerBound_le_goodMass :=
    cert.singleNumeratorSuccessLowerBound_le_goodMass d hd

end ShorSourcePhaseMassCertificate

end

end OrderFinding
end QuantumAlg
