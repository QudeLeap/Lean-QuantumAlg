/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.PMF
import all QuantumAlg.Primitives.ShortDLP.BornProbability.Distribution
import all QuantumAlg.Util.Complex
import all QuantumAlg.Util.NumberTheory.CenteredResidue
import all QuantumAlg.Util.Real.ReciprocalSquareTail
import Mathlib.Algebra.Order.Chebyshev

/-!
# Born probabilities for the declared short-discrete-logarithm circuit

The measured distribution comes from the actual native preparation,
model-owned group query, and parallel inverse Fourier readout. The remaining
source probability and success bounds are derived from that distribution.
-/

section

namespace QuantumAlg

open NormalizedVector
open scoped BigOperators

noncomputable section

namespace ShortDLP
namespace BornProbability

/-! ## Centered-frequency events -/


/-- E23's centered `tau`-good predicate on one measured exponent pair.  The
distance is computed modulo `2^(m+ell)` and the accepted window is
`2^(m+tau)` [E23, arxiv-v5.tex:332-337]. -/
def TauGoodPair (params : RegisterParameters) (secret τ : Nat)
    (sample : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) : Prop :=
  NumberTheory.centeredModDistance (2 ^ (params.m + params.ell))
      (secret * sample.1.val + 2 ^ params.m * sample.2.val) ≤
    2 ^ (params.m + τ)

/-- The source-facing centered-distance predicate is exactly the absolute
centered Fourier-frequency window used by the analytic tail bound. -/
lemma tauGoodPair_iff_centeredPhaseFrequency
    (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    TauGoodPair params secret τ (j, k) ↔
      (centeredPhaseFrequency secret j k).natAbs ≤
        2 ^ (params.m + τ) := by
  unfold TauGoodPair centeredPhaseFrequency phaseFrequencyNat firstBits
  rw [NumberTheory.natAbs_centeredResidue (by positivity)]
  simp [Nat.add_comm]

/-- Second-register outcomes outside the centered `tau` window for one fixed
first-register outcome. -/
def tauBadKSet (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) : Finset (Fin (2 ^ params.ell)) := by
  classical
  exact Finset.univ.filter fun k =>
    ¬ TauGoodPair params secret τ (j, k)

/-- The distinct integral lattice points occupied by the bad second-register
outcomes for one fixed first-register outcome. -/
def tauBadFrequencySet (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) : Finset Int :=
  (tauBadKSet params secret τ j).image
    (scaledFrequencyIndex secret j)

/-- A bad second-register outcome lies strictly beyond distance `2^tau` from
the real center of the scaled integer frequency lattice. -/
lemma tauBadK_distance_gt
    (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hk : k ∈ tauBadKSet params secret τ j) :
    (2 : Real) ^ τ <
      |scaledFrequencyCenter secret j -
        (scaledFrequencyIndex secret j k : Real)| := by
  classical
  have hbad : ¬ TauGoodPair params secret τ (j, k) :=
    (Finset.mem_filter.mp hk).2
  have hfrequencyNat :
      2 ^ (params.m + τ) <
        (centeredPhaseFrequency secret j k).natAbs := by
    exact Nat.lt_of_not_ge
      (fun h => hbad ((tauGoodPair_iff_centeredPhaseFrequency
        params secret τ j k).2 h))
  have habsFrequency :
      |(centeredPhaseFrequency secret j k : Real)| =
        ((centeredPhaseFrequency secret j k).natAbs : Real) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hfrequencyReal :
      (2 : Real) ^ (params.m + τ) <
        |(centeredPhaseFrequency secret j k : Real)| := by
    rw [habsFrequency]
    exact_mod_cast hfrequencyNat
  rw [abs_centeredPhaseFrequency_eq_spacing_mul_distance
    secret j k, pow_add] at hfrequencyReal
  have hspacingPos : 0 < (2 : Real) ^ params.m := by positivity
  nlinarith

/-- The bad scaled-frequency lattice has a two-sided reciprocal-square tail
bounded solely by the accepted centered window. -/
lemma tauBadFrequency_reciprocalSquareSum_le
    (params : RegisterParameters) (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) :
    (∑ k ∈ tauBadKSet params secret τ j,
        1 / |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| ^ 2) ≤
      2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2 := by
  classical
  have hinjective : Set.InjOn (scaledFrequencyIndex secret j)
      (tauBadKSet params secret τ j) := by
    intro left _hleft right _hright heq
    exact scaledFrequencyIndex_injective secret j heq
  calc
    (∑ k ∈ tauBadKSet params secret τ j,
        1 / |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| ^ 2) =
      ∑ z ∈ tauBadFrequencySet params secret τ j,
        1 / |scaledFrequencyCenter secret j - (z : Real)| ^ 2 := by
          unfold tauBadFrequencySet
          rw [Finset.sum_image hinjective]
    _ ≤ 2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2 := by
      apply integerReciprocalSquareTail_le
      · positivity
      · intro z hz
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        exact (tauBadK_distance_gt params secret τ j k hk).le

/-- Actual Born probability of one decoded exponent pair, obtained by
marginalizing the unmeasured group workspace. -/
def pairBornProbability {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (sample : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) : ENNReal :=
  ∑ workspace : Fin (2 ^ params.workspaceBits),
    ENNReal.ofReal
      (‖circuitAmplitude encoding g x sample.1 sample.2 workspace‖ ^ 2)

/-- Real source weight corresponding to Eq. (3), before embedding the
nonnegative result into `ENNReal`. -/
def pairSourceWeight {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) : Real :=
  ∑ index : Fin (oracleFiberSpan params secret),
    (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
      ‖exponentFiberIntervalSum secret
        (oracleExponentAtIndex params secret index) j k‖ ^ 2

/-- Every source Eq. (3) pair weight is nonnegative. -/
lemma pairSourceWeight_nonneg {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell)) :
    0 ≤ pairSourceWeight secret j k := by
  unfold pairSourceWeight
  positivity

/-- The first-register marginal of the source Eq. (3) distribution is exactly
uniform.  This is derived from the inverse-QFT Parseval identity on every
integer-exponent fiber and the exact partition of all exponent inputs; no
uniformity assumption is attached to the probability model. -/
lemma sum_pairSourceWeight_fixedFirst_eq
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) :
    (∑ k : Fin (2 ^ params.ell), pairSourceWeight secret j k) =
      ((2 : Real) ^ firstBits params)⁻¹ := by
  classical
  let normalization : Real :=
    ((2 : Real) ^ (2 * (params.m + 2 * params.ell)))⁻¹
  have hsumReal :
      (∑ index : Fin (oracleFiberSpan params secret),
        ((exponentFiberBSet (params := params) secret
          (oracleExponentAtIndex params secret index)).card : Real)) =
        (2 : Real) ^ firstBits params * (2 : Real) ^ params.ell := by
    exact_mod_cast sum_card_exponentFiberBSet params secret
  have hpower :
      (2 : Real) ^ (2 * (params.m + 2 * params.ell)) =
        ((2 : Real) ^ firstBits params) ^ 2 *
          ((2 : Real) ^ params.ell) ^ 2 := by
    rw [show 2 * (params.m + 2 * params.ell) =
        2 * (params.m + params.ell) + 2 * params.ell by omega,
      pow_add,
      show 2 * (params.m + params.ell) =
        (params.m + params.ell) * 2 by omega,
      show 2 * params.ell = params.ell * 2 by omega,
      pow_mul, pow_mul]
    simp only [firstBits, Nat.add_comm]
  unfold pairSourceWeight
  rw [Finset.sum_comm]
  calc
    (∑ index : Fin (oracleFiberSpan params secret),
        ∑ k : Fin (2 ^ params.ell),
          (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
            ‖exponentFiberIntervalSum secret
              (oracleExponentAtIndex params secret index) j k‖ ^ 2) =
      normalization *
        ∑ index : Fin (oracleFiberSpan params secret),
          ∑ k : Fin (2 ^ params.ell),
            ‖exponentFiberIntervalSum secret
              (oracleExponentAtIndex params secret index) j k‖ ^ 2 := by
        dsimp [normalization]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _hindex
        rw [Finset.mul_sum]
    _ = normalization *
        ∑ index : Fin (oracleFiberSpan params secret),
          ((2 : Real) ^ params.ell *
            (exponentFiberBSet (params := params) secret
              (oracleExponentAtIndex params secret index)).card) := by
        congr 1
        apply Finset.sum_congr rfl
        intro index _hindex
        exact sum_normSq_exponentFiberIntervalSum secret
          (oracleExponentAtIndex params secret index) j
    _ = normalization * ((2 : Real) ^ params.ell *
        ∑ index : Fin (oracleFiberSpan params secret),
          ((exponentFiberBSet (params := params) secret
            (oracleExponentAtIndex params secret index)).card : Real)) := by
      congr 1
      calc
        (∑ index : Fin (oracleFiberSpan params secret),
            (2 : Real) ^ params.ell *
              (exponentFiberBSet (params := params) secret
                (oracleExponentAtIndex params secret index)).card) =
          ∑ index : Fin (oracleFiberSpan params secret),
            ((exponentFiberBSet (params := params) secret
              (oracleExponentAtIndex params secret index)).card : Real) *
                (2 : Real) ^ params.ell := by
            apply Finset.sum_congr rfl
            intro index _hindex
            ring
        _ = (∑ index : Fin (oracleFiberSpan params secret),
              ((exponentFiberBSet (params := params) secret
                (oracleExponentAtIndex params secret index)).card : Real)) *
              (2 : Real) ^ params.ell := by
            rw [Finset.sum_mul]
        _ = (2 : Real) ^ params.ell *
            ∑ index : Fin (oracleFiberSpan params secret),
              ((exponentFiberBSet (params := params) secret
                (oracleExponentAtIndex params secret index)).card : Real) := by
          ring
    _ = normalization * ((2 : Real) ^ params.ell *
        ((2 : Real) ^ firstBits params * (2 : Real) ^ params.ell)) := by
      rw [hsumReal]
    _ = ((2 : Real) ^ firstBits params)⁻¹ := by
      dsimp [normalization]
      rw [hpower]
      field_simp

/-- Every Ekerå–Håstad narrow-good measured pair has source probability at
least `2^(-m-ℓ-2)`.  This is derived from the actual contiguous Fourier
fibers: the quarter-circle estimate supplies one half of each squared fiber
cardinality, while Cauchy–Schwarz supplies the global fiber-square mass
[EH17, source.tex:645-745]. -/
lemma narrowGoodPairSourceWeight_ge
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hm : 2 ≤ params.m) (hsecret : secret < 2 ^ params.m)
    (hgood : (centeredPhaseFrequency secret j k).natAbs ≤
      2 ^ (params.m - 2)) :
    ((2 : Real) ^ (params.m + params.ell + 2))⁻¹ ≤
      pairSourceWeight secret j k := by
  let normalization : Real :=
    ((2 : Real) ^ (2 * (params.m + 2 * params.ell)))⁻¹
  let fiberCard : Fin (oracleFiberSpan params secret) → Real :=
    fun index =>
      ((exponentFiberBSet (params := params) secret
        (oracleExponentAtIndex params secret index)).card : Real)
  have hcauchy :=
    sq_sum_card_exponentFiberBSet_div_le params secret hsecret
  have hperFiber (index : Fin (oracleFiberSpan params secret)) :
      normalization * (fiberCard index ^ 2 / 2) ≤
        normalization *
          ‖exponentFiberIntervalSum secret
            (oracleExponentAtIndex params secret index) j k‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact norm_exponentFiberIntervalSum_sq_ge_half_card
      secret (oracleExponentAtIndex params secret index) j k hm hgood
  have hsumLower :
      normalization *
          ((∑ index : Fin (oracleFiberSpan params secret),
            fiberCard index ^ 2) / 2) ≤
        pairSourceWeight secret j k := by
    calc
      normalization *
          ((∑ index : Fin (oracleFiberSpan params secret),
            fiberCard index ^ 2) / 2) =
        (normalization / 2) *
          ∑ index : Fin (oracleFiberSpan params secret),
            fiberCard index ^ 2 := by ring
      _ = ∑ index : Fin (oracleFiberSpan params secret),
          (normalization / 2) * fiberCard index ^ 2 := by
            rw [Finset.mul_sum]
      _ = ∑ index : Fin (oracleFiberSpan params secret),
          normalization * (fiberCard index ^ 2 / 2) := by
        apply Finset.sum_congr rfl
        intro index _hindex
        ring
      _ ≤ ∑ index : Fin (oracleFiberSpan params secret),
          normalization *
            ‖exponentFiberIntervalSum secret
              (oracleExponentAtIndex params secret index) j k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro index _hindex
        exact hperFiber index
      _ = pairSourceWeight secret j k := by
        rfl
  have hscaledCauchy :
      normalization *
          (((((2 : Real) ^ firstBits params) *
              (2 : Real) ^ params.ell) ^ 2) /
            (2 * (2 : Real) ^ firstBits params) / 2) ≤
        normalization *
          ((∑ index : Fin (oracleFiberSpan params secret),
            fiberCard index ^ 2) / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right hcauchy
    norm_num
  have hlower := hscaledCauchy.trans hsumLower
  have hinputPow :
      (2 : Real) ^ firstBits params * (2 : Real) ^ params.ell =
        (2 : Real) ^ (params.m + 2 * params.ell) := by
    rw [← pow_add]
    unfold firstBits
    congr 1
    omega
  have hnormalizationPow :
      (2 : Real) ^ (2 * (params.m + 2 * params.ell)) =
        ((2 : Real) ^ (params.m + 2 * params.ell)) ^ 2 := by
    rw [Nat.mul_comm 2, pow_mul]
  have houtputPow :
      (2 : Real) ^ (params.m + params.ell + 2) =
        4 * (2 : Real) ^ firstBits params := by
    rw [show params.m + params.ell + 2 =
        2 + firstBits params by unfold firstBits; omega, pow_add]
    norm_num
  dsimp only [normalization, fiberCard] at hlower
  rw [hinputPow, hnormalizationPow] at hlower
  calc
    ((2 : Real) ^ (params.m + params.ell + 2))⁻¹ =
        (((2 : Real) ^ (params.m + 2 * params.ell)) ^ 2)⁻¹ *
          ((((2 : Real) ^ (params.m + 2 * params.ell)) ^ 2) /
            (2 * (2 : Real) ^ firstBits params) / 2) := by
      rw [houtputPow]
      field_simp
      norm_num
    _ ≤ pairSourceWeight secret j k := hlower

/-- Every selected core atom has the source's uniform pointwise Fourier
minorization floor. -/
lemma exactNarrowGoodCore_pairSourceWeight_ge
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m)
    {pair : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)}
    (hpair : pair ∈ exactNarrowGoodCore secret hm hsecretPos hsecretLt) :
    ((2 : Real) ^ (params.m + params.ell + 2))⁻¹ ≤
      pairSourceWeight secret pair.1 pair.2 := by
  classical
  apply narrowGoodPairSourceWeight_ge secret pair.1 pair.2 hm hsecretLt
  exact (Finset.mem_filter.mp
    (exactNarrowGoodCore_mem_narrowGoodPairs secret hm hsecretPos hsecretLt
      hpair)).2

/-- Total source-formula mass of the narrow Ekerå–Håstad event. -/
def narrowGoodSourceWeight {params : RegisterParameters} (secret : Nat) : Real :=
  ∑ pair ∈ narrowGoodPairs params secret,
    pairSourceWeight secret pair.1 pair.2

/-- The source Eq. (3) assigns at least one eighth of its total mass to the
narrow good-pair event.  This is the exact product of at least
`2^(m+ℓ-1)` good pairs and the per-pair floor `2^(-m-ℓ-2)`
[EH17, source.tex:540-745]. -/
lemma narrowGoodSourceWeight_ge_oneEighth
    {params : RegisterParameters} (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m) :
    (1 / 8 : Real) ≤ narrowGoodSourceWeight (params := params) secret := by
  classical
  let goodPairs := narrowGoodPairs params secret
  let pointFloor : Real :=
    ((2 : Real) ^ (params.m + params.ell + 2))⁻¹
  have hcardNat : 2 ^ (firstBits params - 1) ≤ goodPairs.card := by
    exact narrowGoodPair_card_ge secret hm hsecretPos hsecretLt
  have hcardReal :
      ((2 ^ (firstBits params - 1) : Nat) : Real) ≤
        (goodPairs.card : Real) := by
    exact_mod_cast hcardNat
  have hpointFloorNonneg : 0 ≤ pointFloor := by
    dsimp [pointFloor]
    positivity
  have hfloorProduct :
      (1 / 8 : Real) =
        ((2 ^ (firstBits params - 1) : Nat) : Real) * pointFloor := by
    dsimp [pointFloor]
    rw [show params.m + params.ell + 2 =
        (firstBits params - 1) + 3 by unfold firstBits; omega, pow_add]
    norm_num [Nat.cast_pow]
    field_simp
  calc
    (1 / 8 : Real) =
        ((2 ^ (firstBits params - 1) : Nat) : Real) * pointFloor :=
      hfloorProduct
    _ ≤ (goodPairs.card : Real) * pointFloor :=
      mul_le_mul_of_nonneg_right hcardReal hpointFloorNonneg
    _ = ∑ _pair ∈ goodPairs, pointFloor := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ pair ∈ goodPairs,
        pairSourceWeight secret pair.1 pair.2 := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact narrowGoodPairSourceWeight_ge secret pair.1 pair.2 hm hsecretLt
        (by simpa [goodPairs, narrowGoodPairs, NarrowGoodPair] using
          (Finset.mem_filter.mp hpair).2)
    _ = narrowGoodSourceWeight (params := params) secret := rfl

/-- Source Eq. (3) for the actual production circuit: the probability of one
measured pair is the common `2⁻²⁽ᵐ⁺²ˡ⁾` normalization times the sum of squared
contiguous Fourier fibers over the complete canonical exponent interval.
Nothing in this formula is supplied as detached probability metadata. -/
lemma pairBornProbability_eq_sourceFormula
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    pairBornProbability encoding g x (j, k) =
      ∑ index : Fin (oracleFiberSpan params secret),
        ENNReal.ofReal
          ((((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
            ‖exponentFiberIntervalSum secret
              (oracleExponentAtIndex params secret index) j k‖ ^ 2) := by
  rw [pairBornProbability,
    workspaceMarginal_eq_exponentIndexSum
      encoding g x secret j k htarget horder]
  apply Finset.sum_congr rfl
  intro index _hindex
  change ENNReal.ofReal
      (‖circuitAmplitude encoding g x j k
        (encodeUnit encoding
          (g ^ oracleExponentAtIndex params secret index))‖ ^ 2) = _
  rw [normSq_circuitAmplitude_at_exponentIndex_eq_sourceFormula
    encoding g x secret index j k htarget horder]

/-- The actual pair probability is the nonnegative-real embedding of the same
source Eq. (3) weight. -/
lemma pairBornProbability_eq_ofReal_pairSourceWeight
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    pairBornProbability encoding g x (j, k) =
      ENNReal.ofReal (pairSourceWeight secret j k) := by
  rw [pairBornProbability_eq_sourceFormula
    encoding g x secret j k htarget horder]
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro index _hindex
  positivity

/-- The actual circuit's first-register marginal is uniform.  The equality is
the `ENNReal` image of `sum_pairSourceWeight_fixedFirst_eq`, hence is derived
from the circuit amplitudes and inverse-QFT unitarity rather than imposed on a
detached measurement model. -/
lemma sum_pairBornProbability_fixedFirst_eq
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (j : Fin (2 ^ firstBits params))
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    (∑ k : Fin (2 ^ params.ell),
        pairBornProbability encoding g x (j, k)) =
      ENNReal.ofReal (((2 : Real) ^ firstBits params)⁻¹) := by
  simp_rw [pairBornProbability_eq_ofReal_pairSourceWeight
    encoding g x secret _ _ htarget horder]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [sum_pairSourceWeight_fixedFirst_eq]
  · intro k _hk
    exact pairSourceWeight_nonneg secret j k

/-- Eq. (3) together with the contiguous-fiber estimate bounds one pair by
the number of integer exponent fibers times one reciprocal-frequency term. -/
lemma pairSourceWeight_le_fiberSpan_mul
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hfrequency : centeredPhaseFrequency secret j k ≠ 0) :
    pairSourceWeight secret j k ≤
      (oracleFiberSpan params secret : Real) *
        ((((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          (((2 ^ firstBits params : Nat) : Real) /
            (2 * ((centeredPhaseFrequency secret j k).natAbs : Real))) ^ 2) := by
  unfold pairSourceWeight
  calc
    (∑ index : Fin (oracleFiberSpan params secret),
        (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          ‖exponentFiberIntervalSum secret
            (oracleExponentAtIndex params secret index) j k‖ ^ 2) ≤
      ∑ _index : Fin (oracleFiberSpan params secret),
        (((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          (((2 ^ firstBits params : Nat) : Real) /
            (2 * ((centeredPhaseFrequency secret j k).natAbs : Real))) ^ 2 := by
      apply Finset.sum_le_sum
      intro index _hindex
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
          (norm_exponentFiberIntervalSum_le secret
            (oracleExponentAtIndex params secret index) j k hfrequency)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin]

/-- Under the short-logarithm range hypothesis, one measured pair has the
explicit inverse-square centered-frequency envelope. -/
lemma pairSourceWeight_le_centeredFrequency
    {params : RegisterParameters} (secret : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hsecret : secret < 2 ^ params.m)
    (hfrequency : centeredPhaseFrequency secret j k ≠ 0) :
    pairSourceWeight secret j k ≤
      ((2 ^ firstBits params : Nat) : Real) /
        (2 * ((2 ^ params.ell : Nat) : Real) ^ 2 *
          ((centeredPhaseFrequency secret j k).natAbs : Real) ^ 2) := by
  have hspanNat :=
    oracleFiberSpan_le_two_mul_firstRegister params secret hsecret
  have hspanReal :
      (oracleFiberSpan params secret : Real) ≤
        2 * ((2 ^ firstBits params : Nat) : Real) := by
    exact_mod_cast hspanNat
  have hfrequencyPos :
      0 < ((centeredPhaseFrequency secret j k).natAbs : Real) := by
    exact_mod_cast (Int.natAbs_pos.mpr hfrequency)
  have hpower :
      (2 : Real) ^ (2 * (params.m + 2 * params.ell)) =
        ((2 : Real) ^ firstBits params) ^ 2 *
          ((2 : Real) ^ params.ell) ^ 2 := by
    rw [show 2 * (params.m + 2 * params.ell) =
        2 * (params.m + params.ell) + 2 * params.ell by omega,
      pow_add,
      show 2 * (params.m + params.ell) =
        (params.m + params.ell) * 2 by omega,
      show 2 * params.ell = params.ell * 2 by omega,
      pow_mul, pow_mul]
    simp only [firstBits, Nat.add_comm]
  calc
    pairSourceWeight secret j k ≤
      (oracleFiberSpan params secret : Real) *
        ((((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          (((2 ^ firstBits params : Nat) : Real) /
            (2 * ((centeredPhaseFrequency secret j k).natAbs : Real))) ^ 2) :=
        pairSourceWeight_le_fiberSpan_mul secret j k hfrequency
    _ ≤ (2 * ((2 ^ firstBits params : Nat) : Real)) *
        ((((2 : Real) ^ (2 * (params.m + 2 * params.ell))))⁻¹ *
          (((2 ^ firstBits params : Nat) : Real) /
            (2 * ((centeredPhaseFrequency secret j k).natAbs : Real))) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hspanReal (by positivity)
    _ = ((2 ^ firstBits params : Nat) : Real) /
        (2 * ((2 ^ params.ell : Nat) : Real) ^ 2 *
          ((centeredPhaseFrequency secret j k).natAbs : Real) ^ 2) := by
      rw [hpower]
      norm_num
      field_simp [ne_of_gt hfrequencyPos]
      simp only [sq_abs]

/-- After scaling the centered frequency by the `2^m` lattice spacing, one
bad pair has a universal reciprocal-square envelope. -/
lemma pairSourceWeight_le_scaledDistance
    {params : RegisterParameters} (secret τ : Nat)
    (j : Fin (2 ^ firstBits params)) (k : Fin (2 ^ params.ell))
    (hsecret : secret < 2 ^ params.m)
    (hk : k ∈ tauBadKSet params secret τ j) :
    pairSourceWeight secret j k ≤
      (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (1 / |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| ^ 2) := by
  have hdistancePos : 0 <
      |scaledFrequencyCenter secret j -
        (scaledFrequencyIndex secret j k : Real)| :=
    (pow_pos (by norm_num : (0 : Real) < 2) τ).trans
      (tauBadK_distance_gt params secret τ j k hk)
  have hfrequencyAbsPos :
      0 < |(centeredPhaseFrequency secret j k : Real)| := by
    rw [abs_centeredPhaseFrequency_eq_spacing_mul_distance secret j k]
    positivity
  have hfrequency : centeredPhaseFrequency secret j k ≠ 0 := by
    intro hzero
    rw [hzero] at hfrequencyAbsPos
    norm_num at hfrequencyAbsPos
  have habsFrequency :
      |(centeredPhaseFrequency secret j k : Real)| =
        ((centeredPhaseFrequency secret j k).natAbs : Real) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hnatAbsEq :
      ((centeredPhaseFrequency secret j k).natAbs : Real) =
        (2 : Real) ^ params.m *
          |scaledFrequencyCenter secret j -
            (scaledFrequencyIndex secret j k : Real)| := by
    rw [← habsFrequency]
    exact abs_centeredPhaseFrequency_eq_spacing_mul_distance secret j k
  have hfirstBitsCast :
      ((2 ^ firstBits params : Nat) : Real) =
        (2 : Real) ^ params.m * (2 : Real) ^ params.ell := by
    norm_num [firstBits, pow_add]
    ring
  have hellCast :
      ((2 ^ params.ell : Nat) : Real) = (2 : Real) ^ params.ell := by
    norm_num
  calc
    pairSourceWeight secret j k ≤
        ((2 ^ firstBits params : Nat) : Real) /
          (2 * ((2 ^ params.ell : Nat) : Real) ^ 2 *
            ((centeredPhaseFrequency secret j k).natAbs : Real) ^ 2) :=
      pairSourceWeight_le_centeredFrequency secret j k hsecret hfrequency
    _ = (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (1 / |scaledFrequencyCenter secret j -
          (scaledFrequencyIndex secret j k : Real)| ^ 2) := by
      rw [hnatAbsEq, hfirstBitsCast, hellCast]
      field_simp [ne_of_gt hdistancePos]

/-- For one fixed first-register result, the total source weight of all bad
second-register results is controlled by the two-sided integer tail. -/
lemma tauBadPairSourceWeight_fixedFirst_le
    {params : RegisterParameters} (secret τ : Nat)
    (j : Fin (2 ^ firstBits params))
    (hsecret : secret < 2 ^ params.m) :
    (∑ k ∈ tauBadKSet params secret τ j,
        pairSourceWeight secret j k) ≤
      (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2) := by
  calc
    (∑ k ∈ tauBadKSet params secret τ j,
        pairSourceWeight secret j k) ≤
      ∑ k ∈ tauBadKSet params secret τ j,
        (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
          (1 / |scaledFrequencyCenter secret j -
            (scaledFrequencyIndex secret j k : Real)| ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact pairSourceWeight_le_scaledDistance secret τ j k hsecret hk
    _ = (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (∑ k ∈ tauBadKSet params secret τ j,
          1 / |scaledFrequencyCenter secret j -
            (scaledFrequencyIndex secret j k : Real)| ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
        (2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
        (tauBadFrequency_reciprocalSquareSum_le params secret τ j)
      positivity

/-- Total source-formula weight of all centered-window failures. -/
def tauBadSourceWeight {params : RegisterParameters} (secret τ : Nat) : Real :=
  ∑ j : Fin (2 ^ firstBits params),
    ∑ k ∈ tauBadKSet params secret τ j,
      pairSourceWeight secret j k

/-- Summing the fixed-first-register tail over the complete first register
cancels the Fourier normalization and leaves the universal failure envelope
`2^-tau + 2^-2tau`. -/
lemma tauBadSourceWeight_le
    {params : RegisterParameters} (secret τ : Nat)
    (hsecret : secret < 2 ^ params.m) :
    tauBadSourceWeight (params := params) secret τ ≤
      1 / (2 : Real) ^ τ + 1 / ((2 : Real) ^ τ) ^ 2 := by
  have hfirstBitsPos :
      0 < ((2 ^ firstBits params : Nat) : Real) := by positivity
  have hrhoPos : 0 < (2 : Real) ^ τ := by positivity
  unfold tauBadSourceWeight
  calc
    (∑ j : Fin (2 ^ firstBits params),
        ∑ k ∈ tauBadKSet params secret τ j,
          pairSourceWeight secret j k) ≤
      ∑ _j : Fin (2 ^ firstBits params),
        (1 / (2 * ((2 ^ firstBits params : Nat) : Real))) *
          (2 / (2 : Real) ^ τ + 2 / ((2 : Real) ^ τ) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact tauBadPairSourceWeight_fixedFirst_le secret τ j hsecret
    _ = 1 / (2 : Real) ^ τ +
        1 / ((2 : Real) ^ τ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin]
      field_simp [ne_of_gt hfirstBitsPos, ne_of_gt hrhoPos]

/-- The actual terminal PMF at the canonical encoding of `(j,k)` is exactly
the same circuit's workspace-marginal probability. -/
lemma shortDLPBornOutcomeProbability_eq_pairBornProbability
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (sample : Fin (2 ^ firstBits params) × Fin (2 ^ params.ell)) :
    (measurement params).outcomePMF (evolvedState encoding g x)
        (shortDLPMeasurementOutcome params (prodEquiv sample)) =
      pairBornProbability encoding g x sample := by
  exact shortDLPBornOutcomeProbability_eq_workspaceMarginal
    encoding g x sample.1 sample.2

/-- First-register marginal of the actual terminal Born distribution.  This
is a projection of the measured circuit output, not a detached sampler. -/
def firstRegisterBornPMF {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) : PMF (Fin (2 ^ firstBits params)) :=
  ((measurement params).outcomePMF (evolvedState encoding g x)).map
    fun outcome => (decodeOutcome params outcome).1

/-- The first-register marginal of the actual short-DLP circuit is exactly
uniform.  The proof reindexes terminal bit strings by the measured register
pair and then uses inverse-QFT Parseval on every fixed first-register value. -/
lemma firstRegisterBornPMF_eq_uniform
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    firstRegisterBornPMF encoding g x =
      PMF.uniformOfFintype (Fin (2 ^ firstBits params)) := by
  classical
  apply PMF.ext
  intro j
  have hmarginal :
      firstRegisterBornPMF encoding g x j =
        ∑ k : Fin (2 ^ params.ell),
          pairBornProbability encoding g x (j, k) := by
    rw [← PMF.toOuterMeasure_apply_singleton]
    rw [firstRegisterBornPMF, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_apply_fintype]
    let e : Fin (2 ^ (firstBits params + params.ell)) ≃ Outcome params :=
      Equiv.ofBijective (shortDLPMeasurementOutcome params)
        (shortDLPMeasurementOutcome_bijective params)
    rw [← Equiv.sum_comp e,
      ← Equiv.sum_comp
        (prodEquiv (m := firstBits params) (n := params.ell)),
      Fintype.sum_prod_type]
    simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
      Set.mem_preimage, Set.mem_singleton_iff,
      decodeOutcome_shortDLPMeasurementOutcome, Equiv.symm_apply_apply]
    simp_rw [shortDLPBornOutcomeProbability_eq_pairBornProbability]
    simp
  rw [hmarginal,
    sum_pairBornProbability_fixedFirst_eq
      encoding g x secret j htarget horder]
  simp [PMF.uniformOfFintype_apply, ENNReal.ofReal_inv_of_pos]

/-! ## Actual narrow-good and tau-good event masses -/

/-- Mass of the narrow Ekerå–Håstad good-pair event in the actual terminal
distribution of the production short-DLP circuit. -/
def narrowGoodBornMass {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat) : ENNReal :=
  ((measurement params).outcomePMF (evolvedState encoding g x)).toOuterMeasure
    {outcome | NarrowGoodPair params secret (decodeOutcome params outcome)}

/-- Reindex the actual terminal narrow-good event by the canonical measured
pair.  This identifies the PMF event with the same finite set used by the
source Eq. (3) count. -/
lemma narrowGoodBornMass_eq_pairSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat) :
    narrowGoodBornMass encoding g x secret =
      ∑ pair ∈ narrowGoodPairs params secret,
        pairBornProbability encoding g x pair := by
  classical
  let e : Fin (2 ^ (firstBits params + params.ell)) ≃ Outcome params :=
    Equiv.ofBijective (shortDLPMeasurementOutcome params)
      (shortDLPMeasurementOutcome_bijective params)
  rw [narrowGoodBornMass, PMF.toOuterMeasure_apply_fintype,
    ← Equiv.sum_comp e,
    ← Equiv.sum_comp
      (prodEquiv (m := firstBits params) (n := params.ell))]
  simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, decodeOutcome_shortDLPMeasurementOutcome,
    Equiv.symm_apply_apply]
  simp_rw [shortDLPBornOutcomeProbability_eq_pairBornProbability]
  unfold narrowGoodPairs
  rw [Finset.sum_filter]

/-- The actual narrow-good Born mass is the nonnegative-real embedding of the
source Eq. (3) narrow-good weight; no detached probability model is used. -/
lemma narrowGoodBornMass_eq_ofReal_sourceWeight
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    narrowGoodBornMass encoding g x secret =
      ENNReal.ofReal
        (narrowGoodSourceWeight (params := params) secret) := by
  rw [narrowGoodBornMass_eq_pairSum]
  simp_rw [pairBornProbability_eq_ofReal_pairSourceWeight
    encoding g x secret _ _ htarget horder]
  unfold narrowGoodSourceWeight
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro pair _hpair
  exact pairSourceWeight_nonneg secret pair.1 pair.2

/-- One execution of the actual production short-DLP circuit lands in the
narrow Ekerå–Håstad good-pair event with probability at least `1/8`
[EH17, source.tex:540-745]. -/
lemma narrowGoodBornMass_ge_oneEighth
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (hm : 2 ≤ params.m) (hsecretPos : 0 < secret)
    (hsecretLt : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    ENNReal.ofReal (1 / 8 : Real) ≤
      narrowGoodBornMass encoding g x secret := by
  rw [narrowGoodBornMass_eq_ofReal_sourceWeight
    encoding g x secret htarget horder]
  exact ENNReal.ofReal_le_ofReal
    (narrowGoodSourceWeight_ge_oneEighth secret hm hsecretPos hsecretLt)

/-- Mass of the `tau`-good event in the actual terminal distribution of the
production short-DLP circuit.  No detached probability model or lower bound is
an input. -/
def tauGoodBornMass {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) : ENNReal :=
  ((measurement params).outcomePMF (evolvedState encoding g x)).toOuterMeasure
    {outcome | TauGoodPair params secret τ (decodeOutcome params outcome)}

/-- Mass of the complementary centered-window failure event in the same actual
terminal distribution. -/
def tauBadBornMass {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) : ENNReal :=
  ((measurement params).outcomePMF (evolvedState encoding g x)).toOuterMeasure
    {outcome | ¬ TauGoodPair params secret τ (decodeOutcome params outcome)}

/-- Reindex the actual terminal event mass by the canonical `(j,k)` basis.
This is the source-facing finite sum used by the Fourier-tail argument
[E23, arxiv-v5.tex:233-266,382-393]. -/
lemma tauGoodBornMass_eq_pairSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) :
    tauGoodBornMass encoding g x secret τ =
      ∑ leftRight : Fin (2 ^ (firstBits params + params.ell)),
        Set.indicator
          {leftRight |
            TauGoodPair params secret τ (prodEquiv.symm leftRight)}
          (fun leftRight =>
            pairBornProbability encoding g x (prodEquiv.symm leftRight))
          leftRight := by
  classical
  let e : Fin (2 ^ (firstBits params + params.ell)) ≃ Outcome params :=
    Equiv.ofBijective (shortDLPMeasurementOutcome params)
      (shortDLPMeasurementOutcome_bijective params)
  rw [tauGoodBornMass, PMF.toOuterMeasure_apply_fintype,
    ← Equiv.sum_comp e]
  simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, decodeOutcome_shortDLPMeasurementOutcome]
  apply Finset.sum_congr rfl
  intro leftRight _hleftRight
  by_cases hgood :
      TauGoodPair params secret τ (prodEquiv.symm leftRight)
  · rw [if_pos hgood, if_pos hgood]
    simpa only [Equiv.apply_symm_apply] using
      shortDLPBornOutcomeProbability_eq_pairBornProbability encoding g x
        (prodEquiv.symm leftRight)
  · rw [if_neg hgood, if_neg hgood]

/-- Reindex the actual bad-event mass as the nested sum over the bad
second-register outcomes for every first-register outcome. -/
lemma tauBadBornMass_eq_pairSum
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) :
    tauBadBornMass encoding g x secret τ =
      ∑ j : Fin (2 ^ firstBits params),
        ∑ k ∈ tauBadKSet params secret τ j,
          pairBornProbability encoding g x (j, k) := by
  classical
  let e : Fin (2 ^ (firstBits params + params.ell)) ≃ Outcome params :=
    Equiv.ofBijective (shortDLPMeasurementOutcome params)
      (shortDLPMeasurementOutcome_bijective params)
  rw [tauBadBornMass, PMF.toOuterMeasure_apply_fintype,
    ← Equiv.sum_comp e,
    ← Equiv.sum_comp
      (prodEquiv (m := firstBits params) (n := params.ell)),
    Fintype.sum_prod_type]
  simp only [e, Equiv.ofBijective_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, decodeOutcome_shortDLPMeasurementOutcome,
    Equiv.symm_apply_apply]
  simp_rw [shortDLPBornOutcomeProbability_eq_pairBornProbability]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold tauBadKSet
  rw [Finset.sum_filter]

/-- The actual bad-event probability is exactly the nonnegative-real embedding
of the source Eq. (3) bad weight. -/
lemma tauBadBornMass_eq_ofReal_sourceWeight
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    tauBadBornMass encoding g x secret τ =
      ENNReal.ofReal (tauBadSourceWeight (params := params) secret τ) := by
  rw [tauBadBornMass_eq_pairSum]
  simp_rw [pairBornProbability_eq_ofReal_pairSourceWeight
    encoding g x secret _ _ htarget horder]
  unfold tauBadSourceWeight
  have hinner (j : Fin (2 ^ firstBits params)) :
      (∑ k ∈ tauBadKSet params secret τ j,
          ENNReal.ofReal (pairSourceWeight secret j k)) =
        ENNReal.ofReal
          (∑ k ∈ tauBadKSet params secret τ j,
            pairSourceWeight secret j k) := by
    symm
    apply ENNReal.ofReal_sum_of_nonneg
    intro k _hk
    exact pairSourceWeight_nonneg secret j k
  simp_rw [hinner]
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro j _hj
  exact Finset.sum_nonneg fun k _hk => pairSourceWeight_nonneg secret j k

/-- The actual terminal failure probability obeys the universal centered-tail
envelope derived from the same circuit's Eq. (3) amplitudes. -/
lemma tauBadBornMass_le
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat)
    (hsecret : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    tauBadBornMass encoding g x secret τ ≤
      ENNReal.ofReal
        (1 / (2 : Real) ^ τ + 1 / ((2 : Real) ^ τ) ^ 2) := by
  rw [tauBadBornMass_eq_ofReal_sourceWeight
    encoding g x secret τ htarget horder]
  exact ENNReal.ofReal_le_ofReal
    (tauBadSourceWeight_le secret τ hsecret)

/-- The good and bad centered-window events are exact complements in the
actual terminal PMF. -/
lemma tauGoodBornMass_eq_one_sub_tauBadBornMass
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret τ : Nat) :
    tauGoodBornMass encoding g x secret τ =
      1 - tauBadBornMass encoding g x secret τ := by
  exact PMF.eventProbability_eq_one_sub_complement
    ((measurement params).outcomePMF (evolvedState encoding g x))
    (fun outcome =>
      TauGoodPair params secret τ (decodeOutcome params outcome))

/-- At the production choice `tau = 4`, the actual centered-window failure
mass is at most `17/256`. -/
lemma tauFourBadBornMass_le_seventeen_over_twoFiftySix
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (hsecret : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    tauBadBornMass encoding g x secret 4 ≤
      ENNReal.ofReal (17 / 256 : Real) := by
  convert tauBadBornMass_le encoding g x secret 4
    hsecret htarget horder using 1
  norm_num

/-- The actual production circuit has centered `tau = 4` good mass at least
`239/256`, with no detached measurement model or assumed probability floor. -/
lemma tauFourGoodBornMass_ge_twoThirtyNine_over_twoFiftySix
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (hsecret : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    ENNReal.ofReal (239 / 256 : Real) ≤
      tauGoodBornMass encoding g x secret 4 := by
  have hbad := tauFourBadBornMass_le_seventeen_over_twoFiftySix
    encoding g x secret hsecret htarget horder
  calc
    ENNReal.ofReal (239 / 256 : Real) =
        ENNReal.ofReal (1 - 17 / 256 : Real) := by norm_num
    _ = ENNReal.ofReal (1 : Real) -
        ENNReal.ofReal (17 / 256 : Real) := by
      rw [ENNReal.ofReal_sub]
      norm_num
    _ = 1 - ENNReal.ofReal (17 / 256 : Real) := by
      rw [ENNReal.ofReal_one]
    _ ≤ 1 - tauBadBornMass encoding g x secret 4 :=
      tsub_le_tsub_left hbad 1
    _ = tauGoodBornMass encoding g x secret 4 :=
      (tauGoodBornMass_eq_one_sub_tauBadBornMass
        encoding g x secret 4).symm

/-- Coarse one-eighth corollary proved here for `tau = 4` using the wider
centered-window analysis [E23, arxiv-v5.tex:334-337,382-393].  The narrow
good-pair event used by the two-sample lattice-recovery analysis above has a
different window [EH17, source.tex:525-532]. -/
lemma tauFourGoodBornMass_ge_oneEighth
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) (secret : Nat)
    (hsecret : secret < 2 ^ params.m)
    (htarget : x = g ^ secret)
    (horder : oracleFiberSpan params secret ≤ orderOf g) :
    ENNReal.ofReal (1 / 8 : Real) ≤
      tauGoodBornMass encoding g x secret 4 := by
  calc
    ENNReal.ofReal (1 / 8 : Real) ≤
        ENNReal.ofReal (239 / 256 : Real) :=
      ENNReal.ofReal_le_ofReal (by norm_num)
    _ ≤ tauGoodBornMass encoding g x secret 4 :=
      tauFourGoodBornMass_ge_twoThirtyNine_over_twoFiftySix
        encoding g x secret hsecret htarget horder

end BornProbability
end ShortDLP

end

end QuantumAlg

end
