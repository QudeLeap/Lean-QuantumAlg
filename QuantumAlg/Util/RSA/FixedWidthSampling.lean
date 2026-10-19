/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.RSA.GeneratorOrder
import all QuantumAlg.Util.RSA.ResidueSampling

/-!
# Fixed-width sampling bounds for RSA units

This module turns the executable fixed-width residue sampler into finite
counting bounds.  It never replaces the sampler by a uniform unit-group PMF:
rejected proposal vectors and vectors containing an exceptional unit
representative are counted separately.
-/

section

namespace QuantumAlg
namespace RSA
namespace FixedWidthSampling

open GeneratorOrder

noncomputable section

/-- The public word width of an exact same-bit RSA modulus is exactly twice
the prime width. -/
lemma modulus_clog_eq_two_mul {b : Nat} (pair : RSAKeyPairBits b)
    (hb : 1 ≤ b) :
    Nat.clog 2 pair.modulus = 2 * b := by
  apply HasExactBitLength.clog_two_eq_of_odd (by omega) pair.modulus_bits
  exact pair.p_odd.mul pair.q_odd

/-- The binary digit count of an exact same-bit RSA modulus is exactly twice
the prime width. -/
lemma modulus_size_eq_two_mul {b : Nat} (pair : RSAKeyPairBits b)
    (hb : 1 ≤ b) :
    Nat.size pair.modulus = 2 * b := by
  apply le_antisymm
  · exact Nat.size_le.mpr pair.modulus_bits.2
  · have hlower : 2 * b - 1 < Nat.size pair.modulus :=
      Nat.lt_size.mpr pair.modulus_bits.1
    omega

/-- Exceptional public units for the selected CRT-coordinate order cutoff. -/
noncomputable def badUnits {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits : Nat) : Finset (ZMod pair.modulus)ˣ := by
  classical
  let _ : NeZero pair.modulus :=
    ⟨Nat.ne_of_gt (Nat.mul_pos pair.p_prime.pos pair.q_prime.pos)⟩
  exact Finset.univ.filter fun unit => CoordinateOrderBad pair tailBits unit

/-- Fixed-width eligible representatives that encode exceptional public
units.  The coprimality witness only constructs the canonical unit; proof
irrelevance ensures it cannot affect membership. -/
noncomputable def badResidueCandidates {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits wordWidth : Nat) : Finset (Fin (2 ^ wordWidth)) := by
  classical
  exact Finset.univ.filter fun candidate =>
    ResidueEligible pair.modulus candidate.val ∧
      ∃ hcoprime : Nat.Coprime candidate.val pair.modulus,
        CoordinateOrderBad pair tailBits
          (ZMod.unitOfCoprime candidate.val hcoprime)

/-- Canonical public unit encoded by one exceptional eligible proposal. -/
noncomputable def badResidueUnit {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits wordWidth : Nat)
    (candidate : ↑(badResidueCandidates pair tailBits wordWidth)) :
    (ZMod pair.modulus)ˣ := by
  classical
  have hbad := (Finset.mem_filter.mp candidate.property).2
  exact ZMod.unitOfCoprime candidate.val.val (Classical.choose hbad.2)

@[simp] lemma badResidueUnit_coe {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits wordWidth : Nat)
    (candidate : ↑(badResidueCandidates pair tailBits wordWidth)) :
    ((badResidueUnit pair tailBits wordWidth candidate :
      (ZMod pair.modulus)ˣ) : ZMod pair.modulus) = candidate.val.val := by
  unfold badResidueUnit
  rw [ZMod.coe_unitOfCoprime]

/-- The canonical unit of an exceptional proposal satisfies the same
coordinate-order predicate. -/
lemma badResidueUnit_bad {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits wordWidth : Nat)
    (candidate : ↑(badResidueCandidates pair tailBits wordWidth)) :
    CoordinateOrderBad pair tailBits
      (badResidueUnit pair tailBits wordWidth candidate) := by
  classical
  have hbad := (Finset.mem_filter.mp candidate.property).2
  unfold badResidueUnit
  exact Classical.choose_spec hbad.2

/-- Distinct eligible natural representatives give distinct units, so the
number of exceptional proposal words is at most the number of exceptional
public units. -/
lemma badResidueCandidates_card_le_badUnits_card
    {b : Nat} (pair : RSAKeyPairBits b) (tailBits wordWidth : Nat) :
    (badResidueCandidates pair tailBits wordWidth).card ≤
      (badUnits pair tailBits).card := by
  classical
  let _ : NeZero pair.modulus :=
    ⟨Nat.ne_of_gt (Nat.mul_pos pair.p_prime.pos pair.q_prime.pos)⟩
  let embed :
      ↑(badResidueCandidates pair tailBits wordWidth) →
        ↑(badUnits pair tailBits) := fun candidate =>
    ⟨badResidueUnit pair tailBits wordWidth candidate,
      by
        simp [badUnits, badResidueUnit_bad]⟩
  have hinjective : Function.Injective embed := by
    intro left right heq
    have hunit : (embed left).val = (embed right).val :=
      congrArg Subtype.val heq
    have hcast :
        ((left.val.val : Nat) : ZMod pair.modulus) =
          ((right.val.val : Nat) : ZMod pair.modulus) := by
      simpa only [embed, badResidueUnit_coe] using congrArg
        (fun unit : (ZMod pair.modulus)ˣ => (unit : ZMod pair.modulus)) hunit
    have hmodEq : left.val.val ≡ right.val.val [MOD pair.modulus] := by
      apply (ZMod.natCast_eq_natCast_iff left.val.val right.val.val
        pair.modulus).mp
      exact hcast
    have hleftLt : left.val.val < pair.modulus :=
      ((Finset.mem_filter.mp left.property).2).1.2
    have hrightLt : right.val.val < pair.modulus :=
      ((Finset.mem_filter.mp right.property).2).1.2
    rw [Nat.ModEq, Nat.mod_eq_of_lt hleftLt,
      Nat.mod_eq_of_lt hrightLt] at hmodEq
    apply Subtype.ext
    apply Fin.ext
    exact hmodEq
  exact Finset.card_le_card_of_injective hinjective

/-- The exceptional-unit carrier fits inside one exact-width proposal word. -/
lemma badUnits_card_le_wordSpace {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits : Nat) :
    (badUnits pair tailBits).card ≤ 2 ^ (2 * b) := by
  let _ : NeZero pair.modulus :=
    ⟨Nat.ne_of_gt (Nat.mul_pos pair.p_prime.pos pair.q_prime.pos)⟩
  calc
    (badUnits pair tailBits).card ≤
        Fintype.card (ZMod pair.modulus)ˣ := Finset.card_le_univ _
    _ = pair.modulus.totient := ZMod.card_units_eq_totient pair.modulus
    _ ≤ pair.modulus := Nat.totient_le pair.modulus
    _ ≤ 2 ^ (2 * b) := Nat.le_of_lt pair.modulus_bits.2

/-- At the exact `2b`-bit word width, rejected values occupy at most the
fraction `513/1024`.  The slack covers both zero and the unused interval above
the odd modulus while retaining a small rational denominator. -/
lemma rejectedResidueFraction_le
    {b : Nat} (pair : RSAKeyPairBits b) (hb : 512 ≤ b) :
    ((rejectedResidueCandidates pair.modulus (2 * b)).card : Real) /
        ((2 ^ (2 * b) : Nat) : Real) ≤ 513 / 1024 := by
  let wordSpace := 2 ^ (2 * b)
  have hmodulusLe : pair.modulus ≤ wordSpace :=
    Nat.le_of_lt pair.modulus_bits.2
  have hcard :
      (rejectedResidueCandidates pair.modulus (2 * b)).card =
        wordSpace - (pair.modulus - 1) := by
    exact rejectedResidueCandidates_card hmodulusLe
  have hwidthPos : 0 < 2 * b := by omega
  have hhalf : wordSpace / 2 = 2 ^ (2 * b - 1) := by
    dsimp [wordSpace]
    conv_lhs =>
      rw [show 2 * b = (2 * b - 1) + 1 by omega, pow_succ]
    simp
  have hhalfLe : wordSpace / 2 ≤ pair.modulus := by
    rw [hhalf]
    exact pair.modulus_bits.1
  have hwordEven : 2 * (wordSpace / 2) = wordSpace := by
    rw [hhalf]
    dsimp [wordSpace]
    conv_rhs =>
      rw [show 2 * b = (2 * b - 1) + 1 by omega, pow_succ]
    simp [Nat.mul_comm]
  have hwordLarge : 1024 ≤ wordSpace := by
    have hpow : 2 ^ 10 ≤ 2 ^ (2 * b) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    norm_num [wordSpace] at hpow ⊢
    exact hpow
  have hscaledNat :
      1024 * (rejectedResidueCandidates pair.modulus (2 * b)).card ≤
        513 * wordSpace := by
    rw [hcard]
    omega
  have hscaledReal :
      (1024 : Real) *
          (rejectedResidueCandidates pair.modulus (2 * b)).card ≤
        513 * (wordSpace : Real) := by
    exact_mod_cast hscaledNat
  have hwordRealPos : (0 : Real) < wordSpace := by positivity
  apply (div_le_div_iff₀ hwordRealPos (by norm_num : (0 : Real) < 1024)).2
  simpa [wordSpace, mul_comm, mul_left_comm, mul_assoc] using hscaledReal

/-- Measuring exceptional representatives against the full proposal-word
space can only decrease their fraction relative to the exact unit group. -/
lemma badUnitsFraction_le_generatorBadFraction
    {b : Nat} (pair : RSAKeyPairBits b) (tailBits : Nat) :
    ((badUnits pair tailBits).card : Real) /
        ((2 ^ (2 * b) : Nat) : Real) ≤
      generatorBadFraction pair tailBits := by
  classical
  let _ : NeZero pair.p := ⟨pair.p_prime.ne_zero⟩
  let _ : NeZero pair.q := ⟨pair.q_prime.ne_zero⟩
  let _ : NeZero pair.modulus :=
    ⟨Nat.ne_of_gt (Nat.mul_pos pair.p_prime.pos pair.q_prime.pos)⟩
  let _ : Fact pair.p.Prime := ⟨pair.p_prime⟩
  let _ : Fact pair.q.Prime := ⟨pair.q_prime⟩
  have htotalPos : 0 < Fintype.card (ZMod pair.modulus)ˣ :=
    Fintype.card_pos
  have hcardLeNat :
      Fintype.card (ZMod pair.modulus)ˣ ≤ 2 ^ (2 * b) := by
    calc
      Fintype.card (ZMod pair.modulus)ˣ = pair.modulus.totient :=
        ZMod.card_units_eq_totient pair.modulus
      _ ≤ pair.modulus := Nat.totient_le pair.modulus
      _ ≤ 2 ^ (2 * b) := Nat.le_of_lt pair.modulus_bits.2
  have hcardLeReal :
      (Fintype.card (ZMod pair.modulus)ˣ : Real) ≤
        ((2 ^ (2 * b) : Nat) : Real) := by
    exact_mod_cast hcardLeNat
  calc
    ((badUnits pair tailBits).card : Real) /
          ((2 ^ (2 * b) : Nat) : Real) ≤
        ((badUnits pair tailBits).card : Real) /
          (Fintype.card (ZMod pair.modulus)ˣ : Real) :=
      div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast htotalPos) hcardLeReal
    _ = generatorBadFraction pair tailBits := by
      unfold badUnits generatorBadFraction
      rfl

/-- Exact count of packed proposal vectors rejected in every coordinate. -/
lemma allProposalsRejected_card
    (modulus wordWidth wordCount : Nat) :
    ((Finset.univ : Finset (Fin (2 ^ (wordCount * wordWidth)))).filter
      fun bits => ∀ index,
        decodeFixedWidthWords wordWidth wordCount bits index ∈
          rejectedResidueCandidates modulus wordWidth).card =
      (rejectedResidueCandidates modulus wordWidth).card ^ wordCount := by
  exact card_filter_decodeFixedWidthWords_forall_mem
    wordWidth wordCount (rejectedResidueCandidates modulus wordWidth)

/-- Union bound for packed proposal vectors containing at least one
exceptional unit representative. -/
lemma someBadResidueCandidate_card_le
    {b : Nat} (pair : RSAKeyPairBits b) (tailBits wordWidth wordCount : Nat) :
    ((Finset.univ : Finset (Fin (2 ^ (wordCount * wordWidth)))).filter
      fun bits => ∃ index,
        decodeFixedWidthWords wordWidth wordCount bits index ∈
          badResidueCandidates pair tailBits wordWidth).card ≤
      wordCount * (badUnits pair tailBits).card *
        (2 ^ wordWidth) ^ (wordCount - 1) := by
  calc
    ((Finset.univ : Finset (Fin (2 ^ (wordCount * wordWidth)))).filter
        fun bits => ∃ index,
          decodeFixedWidthWords wordWidth wordCount bits index ∈
            badResidueCandidates pair tailBits wordWidth).card ≤
        wordCount * (badResidueCandidates pair tailBits wordWidth).card *
          (2 ^ wordWidth) ^ (wordCount - 1) :=
      card_filter_decodeFixedWidthWords_exists_mem_le wordWidth wordCount _
    _ ≤ wordCount * (badUnits pair tailBits).card *
        (2 ^ wordWidth) ^ (wordCount - 1) := by
      gcongr
      exact badResidueCandidates_card_le_badUnits_card pair tailBits wordWidth

/-- Every decoded proposal is rejected. -/
def AllProposalsRejected (modulus wordWidth wordCount : Nat)
    (bits : Fin (2 ^ (wordCount * wordWidth))) : Prop :=
  ∀ index, decodeFixedWidthWords wordWidth wordCount bits index ∈
    rejectedResidueCandidates modulus wordWidth

/-- At least one decoded proposal is an eligible representative of an
exceptional public unit. -/
def SomeBadResidueProposal {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits wordWidth wordCount : Nat)
    (bits : Fin (2 ^ (wordCount * wordWidth))) : Prop :=
  ∃ index, decodeFixedWidthWords wordWidth wordCount bits index ∈
    badResidueCandidates pair tailBits wordWidth

/-- Conservative finite superset of sampler branches that cannot certify the
short-DLP order threshold. -/
def SamplerExceptional {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits wordWidth wordCount : Nat)
    (bits : Fin (2 ^ (wordCount * wordWidth))) : Prop :=
  AllProposalsRejected pair.modulus wordWidth wordCount bits ∨
    SomeBadResidueProposal pair tailBits wordWidth wordCount bits

/-- Packed proposal words in the conservative sampler exceptional event. -/
noncomputable def samplerExceptionalWords {b : Nat}
    (pair : RSAKeyPairBits b) (tailBits wordWidth wordCount : Nat) :
    Finset (Fin (2 ^ (wordCount * wordWidth))) := by
  classical
  exact Finset.univ.filter fun bits =>
    SamplerExceptional pair tailBits wordWidth wordCount bits

/-- The cardinality of the conservative sampler exceptional event is bounded
by the exact all-rejected count plus the exceptional-coordinate union bound. -/
lemma samplerExceptional_card_le
    {b : Nat} (pair : RSAKeyPairBits b) (tailBits wordWidth wordCount : Nat) :
    (samplerExceptionalWords pair tailBits wordWidth wordCount).card ≤
      (rejectedResidueCandidates pair.modulus wordWidth).card ^ wordCount +
        wordCount * (badUnits pair tailBits).card *
          (2 ^ wordWidth) ^ (wordCount - 1) := by
  classical
  unfold samplerExceptionalWords
  rw [show
    ((Finset.univ : Finset (Fin (2 ^ (wordCount * wordWidth)))).filter
        fun bits => SamplerExceptional pair tailBits wordWidth wordCount bits) =
      ((Finset.univ.filter fun bits =>
        AllProposalsRejected pair.modulus wordWidth wordCount bits) ∪
       (Finset.univ.filter fun bits =>
        SomeBadResidueProposal pair tailBits wordWidth wordCount bits)) by
      ext bits
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union]
      rfl]
  calc
    ((Finset.univ.filter fun bits =>
        AllProposalsRejected pair.modulus wordWidth wordCount bits) ∪
      (Finset.univ.filter fun bits =>
        SomeBadResidueProposal pair tailBits wordWidth wordCount bits)).card ≤
        (Finset.univ.filter fun bits =>
          AllProposalsRejected pair.modulus wordWidth wordCount bits).card +
        (Finset.univ.filter fun bits =>
          SomeBadResidueProposal pair tailBits wordWidth wordCount bits).card :=
      Finset.card_union_le _ _
    _ ≤ (rejectedResidueCandidates pair.modulus wordWidth).card ^ wordCount +
        wordCount * (badUnits pair tailBits).card *
          (2 ^ wordWidth) ^ (wordCount - 1) := by
      gcongr
      · convert (allProposalsRejected_card
          pair.modulus wordWidth wordCount).le using 1
        apply congrArg Finset.card
        ext bits
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      · convert (someBadResidueCandidate_card_le
          pair tailBits wordWidth wordCount) using 1
        · rfl
        · apply congrArg Finset.card
          ext bits
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rfl

/-- Exact exceptional fraction of an executable fixed-width sampler at the
given tail cutoff, word width, and proposal count. -/
noncomputable def samplerExceptionalFractionAt {b : Nat}
    (pair : RSAKeyPairBits b) (tailBits wordWidth wordCount : Nat) : Real :=
  ((samplerExceptionalWords pair tailBits wordWidth wordCount).card : Real) /
    ((2 ^ (wordCount * wordWidth) : Nat) : Real)

/-- Exact failure fraction of the executable sixteen-word fixed-width
sampler, for one same-bit RSA key. -/
noncomputable def samplerExceptionalFraction {b : Nat}
    (pair : RSAKeyPairBits b) : Real :=
  samplerExceptionalFractionAt pair (b / 64) (2 * b) 16

/-- The actual uniform-bit sampler failure is bounded by the sixteenth power
of the single-word rejection bound plus sixteen times the exact bad-unit
fraction. -/
lemma samplerExceptionalFraction_le_exact
    {b : Nat} (pair : RSAKeyPairBits b) (hb : 512 ≤ b) :
    samplerExceptionalFraction pair ≤
      (513 / 1024 : Real) ^ 16 +
        16 * generatorBadFraction pair (b / 64) := by
  let exceptional := samplerExceptionalWords pair (b / 64) (2 * b) 16
  let rejected := rejectedResidueCandidates pair.modulus (2 * b)
  let bad := badUnits pair (b / 64)
  let wordSpace := 2 ^ (2 * b)
  have hcardNat := samplerExceptional_card_le pair (b / 64) (2 * b) 16
  norm_num at hcardNat
  have hcardReal :
      (exceptional.card : Real) ≤
        (rejected.card : Real) ^ 16 +
          16 * (bad.card : Real) * (wordSpace : Real) ^ 15 := by
    exact_mod_cast hcardNat
  have hwordPos : (0 : Real) < wordSpace := by positivity
  have hwordNe : (wordSpace : Real) ≠ 0 := ne_of_gt hwordPos
  have hrejected := rejectedResidueFraction_le pair hb
  have hbad := badUnitsFraction_le_generatorBadFraction pair (b / 64)
  have hdenominator :
      ((2 ^ (16 * (2 * b)) : Nat) : Real) =
        ((2 ^ (2 * b) : Nat) : Real) ^ 16 := by
    exact_mod_cast fixedWidthWords_card (2 * b) 16
  unfold samplerExceptionalFraction samplerExceptionalFractionAt
  rw [hdenominator]
  change (exceptional.card : Real) / (wordSpace : Real) ^ 16 ≤ _
  calc
    (exceptional.card : Real) / (wordSpace : Real) ^ 16 ≤
        ((rejected.card : Real) ^ 16 +
          16 * (bad.card : Real) * (wordSpace : Real) ^ 15) /
            (wordSpace : Real) ^ 16 :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = ((rejected.card : Real) / (wordSpace : Real)) ^ 16 +
        16 * ((bad.card : Real) / (wordSpace : Real)) := by
      field_simp
    _ ≤ (513 / 1024 : Real) ^ 16 +
        16 * generatorBadFraction pair (b / 64) := by
      gcongr

/-- Key-independent analytic upper bound for the executable fixed-width
sampler exceptional fraction. -/
noncomputable def samplerFailureBound (b : Nat) : Real :=
  (513 / 1024 : Real) ^ 16 + 16 * generatorFailureBound b

/-- Effective-width bound used by the public retry calibration. -/
lemma samplerFailureBound_le_effective {b : Nat}
    (hb : GeneratorOrder.effectiveCutoffBits ≤ b) :
    samplerFailureBound b ≤ (513 / 1024 : Real) ^ 16 + 1 / 8 := by
  unfold samplerFailureBound
  have hgenerator := GeneratorOrder.generatorFailureBound_le_oneOver128 hb
  calc
    (513 / 1024 : Real) ^ 16 + 16 * generatorFailureBound b ≤
        (513 / 1024 : Real) ^ 16 + 16 * (1 / 128 : Real) := by
      gcongr
    _ = (513 / 1024 : Real) ^ 16 + 1 / 8 := by ring

/-- Every exact same-bit RSA key in the effective range satisfies the common
fixed-width sampler bound. -/
lemma samplerExceptionalFraction_lt_samplerFailureBound
    {b : Nat} (pair : RSAKeyPairBits b) (hb : 512 ≤ b) :
    samplerExceptionalFraction pair < samplerFailureBound b := by
  calc
    samplerExceptionalFraction pair ≤
        (513 / 1024 : Real) ^ 16 +
          16 * generatorBadFraction pair (b / 64) :=
      samplerExceptionalFraction_le_exact pair hb
    _ < (513 / 1024 : Real) ^ 16 +
        16 * generatorFailureBound b := by
      gcongr
      exact generatorBadFraction_lt_generatorFailureBound pair
    _ = samplerFailureBound b := rfl

/-- The exact exceptional fraction is the actual event mass under the
uniform random-bit source consumed by the executable sampler. -/
lemma uniformBits_samplerExceptionalMass_eq_at
    {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits wordWidth wordCount : Nat) :
    (PMF.uniformOfFintype
      (Fin (2 ^ (wordCount * wordWidth)))).toOuterMeasure
        {bits | SamplerExceptional pair tailBits wordWidth wordCount bits} =
      ENNReal.ofReal
        (samplerExceptionalFractionAt pair tailBits wordWidth wordCount) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  unfold samplerExceptionalFractionAt
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  simp only [ENNReal.ofReal_natCast, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype]
  rfl

/-- Exact sixteen-word specialization used by the same-bit RSA analysis. -/
lemma uniformBits_samplerExceptionalMass_eq
    {b : Nat} (pair : RSAKeyPairBits b) :
    (PMF.uniformOfFintype (Fin (2 ^ (16 * (2 * b))))).toOuterMeasure
        {bits | SamplerExceptional pair (b / 64) (2 * b) 16 bits} =
      ENNReal.ofReal (samplerExceptionalFraction pair) := by
  simpa [samplerExceptionalFraction] using
    uniformBits_samplerExceptionalMass_eq_at pair (b / 64) (2 * b) 16

/-- Exact selector rejection is equivalent to membership in the all-rejected
word-vector event. -/
lemma firstValidResidue_eq_none_iff_allProposalsRejected
    (modulus wordWidth wordCount : Nat)
    (bits : Fin (2 ^ (wordCount * wordWidth))) :
    firstValidResidue
        (classifyResidueProposals modulus
          (decodeFixedWidthWords wordWidth wordCount bits)) = none ↔
      AllProposalsRejected modulus wordWidth wordCount bits := by
  rw [firstValidResidue_classify_eq_none_iff]
  simp only [AllProposalsRejected, rejectedResidueCandidates,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- For a nonexceptional key, every actual sampler branch with no early gcd
factor and insufficient short-DLP order lies in the finite exceptional event.
The proof follows the first selected proposal of the executable sampler. -/
lemma preparedOrderFailure_implies_samplerExceptional
    {b wordWidth wordCount : Nat} (pair : RSAKeyPairBits b)
    (hb : effectiveCutoffBits ≤ b)
    (hkey : Nat.gcd (pair.p - 1) (pair.q - 1) < 2 ^ gcdLossBits b)
    (bits : Fin (2 ^ (wordCount * wordWidth)))
    (hearly :
      (prepareResidueFromBits pair.modulus wordWidth wordCount bits).earlyFactor =
        none)
    (horder : ¬ OrderSufficient b (shortLogSecret pair.p pair.q)
      (orderOf
        (prepareResidueFromBits pair.modulus wordWidth wordCount bits).unit)) :
    SamplerExceptional pair (b / 64) wordWidth wordCount bits := by
  classical
  let prepared := prepareResidueFromBits pair.modulus wordWidth wordCount bits
  let proposals := decodeFixedWidthWords wordWidth wordCount bits
  let selected := firstValidResidue
    (classifyResidueProposals pair.modulus proposals)
  have hearlyPrepared : prepared.earlyFactor = none := by
    simpa [prepared] using hearly
  have horderPrepared :
      ¬ OrderSufficient b (shortLogSecret pair.p pair.q)
        (orderOf prepared.unit) := by
    simpa [prepared] using horder
  by_contra hnotExceptional
  have hnotAll : ¬ AllProposalsRejected
      pair.modulus wordWidth wordCount bits := by
    exact fun hall => hnotExceptional (Or.inl hall)
  have hnotSome : ¬ SomeBadResidueProposal
      pair (b / 64) wordWidth wordCount bits := by
    exact fun hsome => hnotExceptional (Or.inr hsome)
  have hselectedNe : selected ≠ none := by
    intro hnone
    apply hnotAll
    exact (firstValidResidue_eq_none_iff_allProposalsRejected
      pair.modulus wordWidth wordCount bits).mp (by
        simpa [selected, proposals] using hnone)
  cases hselected : selected with
  | none => exact hselectedNe hselected
  | some candidate =>
      have hselected' : firstValidResidue
          (classifyResidueProposals pair.modulus proposals) =
            some candidate := by simpa [selected] using hselected
      obtain ⟨index, hvalue, heligible⟩ :=
        exists_eligible_of_firstValidResidue_classify_eq_some hselected'
      have hprepared : prepared =
          prepareResidue pair.modulus (some candidate) := by
        simp [prepared, prepareResidueFromBits, proposals, hselected']
      have hcoprime : Nat.Coprime candidate pair.modulus := by
        by_contra hnotCoprime
        have hfactor := prepareResidue_some_earlyFactor_of_not_coprime
          pair.modulus candidate heligible.1 heligible.2 hnotCoprime
        rw [hprepared, hfactor] at hearlyPrepared
        simp at hearlyPrepared
      have hunit : prepared.unit =
          ZMod.unitOfCoprime candidate hcoprime := by
        rw [hprepared]
        exact prepareResidue_some_unit_of_coprime
          pair.modulus candidate hcoprime
      have hcoordinateGood : ¬ CoordinateOrderBad pair (b / 64)
          prepared.unit := by
        intro hbad
        apply hnotSome
        refine ⟨index, ?_⟩
        have hcandidateLt : candidate < 2 ^ wordWidth := by
          rw [← hvalue]
          exact (decodeFixedWidthWords wordWidth wordCount bits index).isLt
        have hcandidate :
            decodeFixedWidthWords wordWidth wordCount bits index =
              ⟨candidate, hcandidateLt⟩ := by
          apply Fin.ext
          exact hvalue
        rw [hcandidate]
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, heligible, ?_⟩
        refine ⟨hcoprime, ?_⟩
        rw [hunit] at hbad
        exact hbad
      have hleft :
          (pair.p - 1) / 2 ^ coordinateLossBits b <
            (componentOrders pair prepared.unit).1 := by
        exact Nat.lt_of_not_ge fun hle =>
          hcoordinateGood (Or.inl (by
            simpa [coordinateLossBits] using hle))
      have hright :
          (pair.q - 1) / 2 ^ coordinateLossBits b <
            (componentOrders pair prepared.unit).2 := by
        exact Nat.lt_of_not_ge fun hle =>
          hcoordinateGood (Or.inr (by
            simpa [coordinateLossBits] using hle))
      have hcommon : Nat.gcd (componentOrders pair prepared.unit).1
          (componentOrders pair prepared.unit).2 < 2 ^ gcdLossBits b :=
        (componentOrderGcd_le_keyGcd pair prepared.unit).trans_lt hkey
      have hb9 : 9 ≤ b :=
        (by norm_num [effectiveCutoffBits] : 9 ≤ effectiveCutoffBits).trans hb
      exact horderPrepared <| sampledUnit_orderSufficient pair prepared.unit
        hb9 hleft hright hcommon
        (loss_budget_of_effective hb)

end

end FixedWidthSampling
end RSA
end QuantumAlg

end
