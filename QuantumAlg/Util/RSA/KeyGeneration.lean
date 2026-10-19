/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.PrimeInterval
public import Mathlib.Probability.Distributions.Uniform

/-!
# Same-bit RSA key generation for Ekerå–Håstad

This module defines the one canonical theorem-side distribution used by the
Ekerå–Håstad endpoint.  Both primes have exactly `b` bits and their product
has exactly `2*b` bits.  The public factoring runtime receives only the
resulting modulus; key generation is not charged to its resource ledger.
-/

section

namespace QuantumAlg
namespace RSA

set_option exponentiation.threshold 512

/-- `n` lies in the half-open interval of natural numbers with exactly `b`
binary digits.  The definition is useful even at `b=0`; production RSA
theorems separately require a positive, effective bit length. -/
public def HasExactBitLength (b n : Nat) : Prop :=
  2 ^ (b - 1) ≤ n ∧ n < 2 ^ b

/-- A prime sampled uniformly from the exact `b`-bit interval. -/
abbrev ExactBitPrime (b : Nat) :=
  { p : Fin (2 ^ b) //
      p.val.Prime ∧ Odd p.val ∧ HasExactBitLength b p.val }

/-- The product carrier for two independent exact-`b`-bit prime draws. -/
abbrev IndependentExactBitPrimePair (b : Nat) :=
  ExactBitPrime b × ExactBitPrime b

/-- Rejection predicate that turns two independent exact-width prime draws
into an accepted same-width RSA key: the primes are distinct and their
product has exactly twice the input width. -/
def AcceptsRSAKeyPair {b : Nat}
    (pair : IndependentExactBitPrimePair b) : Prop :=
  pair.1.val.val ≠ pair.2.val.val ∧
    HasExactBitLength (2 * b) (pair.1.val.val * pair.2.val.val)

/-- Accepted carrier of the independent exact-width prime-pair sampler. -/
abbrev AcceptedExactBitPrimePair (b : Nat) :=
  { pair : IndependentExactBitPrimePair b // AcceptsRSAKeyPair pair }

/-- An odd positive-width integer in the exact binary interval has binary
ceiling logarithm equal to that width.  Oddness excludes equality with the
even lower power of two. -/
lemma HasExactBitLength.clog_two_eq_of_odd {b n : Nat}
    (hb : 2 ≤ b) (hbits : HasExactBitLength b n) (hodd : Odd n) :
    Nat.clog 2 n = b := by
  apply le_antisymm
  · exact Nat.clog_le_of_le_pow (Nat.le_of_lt hbits.2)
  · have hpowEven : Even (2 ^ (b - 1)) := by
      exact Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hstrict : 2 ^ (b - 1) < n := by
      exact lt_of_le_of_ne hbits.1 fun heq =>
        (Nat.not_even_iff_odd.mpr hodd) (heq ▸ hpowEven)
    have hpred : b - 1 < Nat.clog 2 n :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hstrict
    omega

/-- Ordered pairs of distinct odd `b`-bit primes whose product has exactly
`2*b` bits.  Finite carriers make uniform key generation an actual finite
PMF rather than an informal sampling instruction. -/
@[expose, implicit_reducible] public def RSAKeyPairBits (b : Nat) :=
  { pair : Fin (2 ^ b) × Fin (2 ^ b) //
      pair.1.val.Prime ∧ pair.2.val.Prime ∧ pair.1.val ≠ pair.2.val ∧
      Odd pair.1.val ∧ Odd pair.2.val ∧
      HasExactBitLength b pair.1.val ∧
      HasExactBitLength b pair.2.val ∧
      HasExactBitLength (2 * b) (pair.1.val * pair.2.val) }

noncomputable instance (b : Nat) : Fintype (RSAKeyPairBits b) := by
  unfold RSAKeyPairBits
  exact Fintype.ofFinite _

/-- Primes in the top quarter of the exact-`b`-bit interval.  Any two
distinct members automatically have a `2*b`-bit product. -/
def topQuarterPrimes (b : Nat) : Finset Nat :=
  Nat.primesLE (2 ^ b) \ Nat.primesLE (3 * 2 ^ (b - 2))

/-- The elementary lower bound used for top-quarter primes is already at
least two throughout the effective range. -/
lemma two_le_topQuarterPrimeCountLowerBound {b : Nat} (hb : 512 ≤ b) :
    2 ≤ NumberTheory.topQuarterPrimeCountLowerBound b := by
  have hlinearAll : ∀ n : Nat, 512 ≤ n → 32 * n ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have hleft : 32 * 512 = 2 ^ (14 : Nat) := by norm_num
        have hpow : 2 ^ (14 : Nat) ≤ 2 ^ (512 : Nat) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [hleft]
        exact hpow
    | succ n hn ih =>
        rw [pow_succ]
        omega
  have hlinear : 32 * b ≤ 2 ^ b := hlinearAll b hb
  unfold NumberTheory.topQuarterPrimeCountLowerBound
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 16 * b)).2
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlinear

/-- The explicit prime-interval theorem, expressed directly as a cardinality
lower bound for the canonical top-quarter carrier. -/
lemma topQuarterPrimeCountLowerBound_le_card {b : Nat} (hb : 512 ≤ b) :
    NumberTheory.topQuarterPrimeCountLowerBound b ≤
      (topQuarterPrimes b).card := by
  rw [topQuarterPrimes, Finset.card_sdiff_of_subset]
  · simpa [Nat.primesLE_card_eq_primeCounting] using
      NumberTheory.topQuarterPrimeCount b hb
  · apply Nat.primesLE_mono
    have hsplit : 2 ^ b = 4 * 2 ^ (b - 2) := by
      calc
        2 ^ b = 2 ^ ((b - 2) + 2) := by congr 1; omega
        _ = 4 * 2 ^ (b - 2) := by rw [pow_add]; ring
    rw [hsplit]
    omega

/-- The floor in the prime-count lower bound loses at most a factor two once
the quotient is at least two. -/
lemma power_le_twice_denominator_mul_topQuarterLowerBound
    {b : Nat} (hb : 512 ≤ b) :
    2 ^ b ≤ 2 * (16 * b) *
      NumberTheory.topQuarterPrimeCountLowerBound b := by
  have hd : 0 < 16 * b := by omega
  have hquot := two_le_topQuarterPrimeCountLowerBound hb
  have hmod := Nat.mod_lt (2 ^ b) hd
  have hdecomp := Nat.div_add_mod (2 ^ b) (16 * b)
  unfold NumberTheory.topQuarterPrimeCountLowerBound at hquot ⊢
  nlinarith

/-- The explicit Chebyshev estimate supplies at least two top-quarter primes
at every effective width used by the Ekerå–Håstad analysis. -/
lemma one_lt_card_topQuarterPrimes {b : Nat} (hb : 512 ≤ b) :
    1 < (topQuarterPrimes b).card := by
  have hlower := topQuarterPrimeCountLowerBound_le_card hb
  have htwo := two_le_topQuarterPrimeCountLowerBound hb
  exact lt_of_lt_of_le (by omega) (htwo.trans hlower)

/-- Same-bit RSA key generation is internally inhabited at every effective
width; no caller-supplied nonemptiness witness is mathematically necessary. -/
lemma rsaKeyPairBits_nonempty {b : Nat} (hb : 512 ≤ b) :
    Nonempty (RSAKeyPairBits b) := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    Finset.one_lt_card.mp (one_lt_card_topQuarterPrimes hb)
  have hpPrime : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
  have hqPrime : q.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hq).1
  have hpLe : p ≤ 2 ^ b :=
    Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
  have hqLe : q ≤ 2 ^ b :=
    Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hq).1
  have hpLower : 3 * 2 ^ (b - 2) < p := by
    by_contra h
    exact (Finset.mem_sdiff.mp hp).2
      (Nat.mem_primesLE.mpr ⟨by omega, hpPrime⟩)
  have hqLower : 3 * 2 ^ (b - 2) < q := by
    by_contra h
    exact (Finset.mem_sdiff.mp hq).2
      (Nat.mem_primesLE.mpr ⟨by omega, hqPrime⟩)
  have hpLt : p < 2 ^ b := by
    refine hpLe.lt_of_ne ?_
    intro heq
    exact Nat.Prime.not_prime_pow (by omega : 2 ≤ b) (heq ▸ hpPrime)
  have hqLt : q < 2 ^ b := by
    refine hqLe.lt_of_ne ?_
    intro heq
    exact Nat.Prime.not_prime_pow (by omega : 2 ≤ b) (heq ▸ hqPrime)
  have hbitPower : 2 ^ (b - 1) = 2 * 2 ^ (b - 2) := by
    rw [show b - 1 = (b - 2) + 1 by omega, pow_succ]
    omega
  have hquarterPositive : 0 < 2 ^ (b - 2) := by positivity
  have hproductPower :
      2 ^ (2 * b - 1) = 8 * (2 ^ (b - 2)) ^ 2 := by
    rw [show 2 * b - 1 = (b - 2) + (b - 2) + 3 by omega,
      pow_add, pow_add]
    ring
  have hproductLower : 2 ^ (2 * b - 1) ≤ p * q := by
    rw [hproductPower]
    nlinarith
  have hproductUpper : p * q < 2 ^ (2 * b) := by
    calc
      p * q < 2 ^ b * 2 ^ b := Nat.mul_lt_mul_of_lt_of_lt hpLt hqLt
      _ = 2 ^ (2 * b) := by rw [← pow_add]; congr 1; omega
  let pFin : Fin (2 ^ b) := ⟨p, hpLt⟩
  let qFin : Fin (2 ^ b) := ⟨q, hqLt⟩
  exact ⟨⟨(pFin, qFin), hpPrime, hqPrime, hpq,
    hpPrime.odd_of_ne_two (by omega),
    hqPrime.odd_of_ne_two (by omega),
    ⟨by simp only [pFin]; rw [hbitPower]; omega, by simpa [pFin]⟩,
    ⟨by simp only [qFin]; rw [hbitPower]; omega, by simpa [qFin]⟩,
    ⟨hproductLower, hproductUpper⟩⟩⟩

/-- First prime of a same-bit RSA key pair. -/
public def RSAKeyPairBits.p {b : Nat} (pair : RSAKeyPairBits b) : Nat :=
  pair.val.1.val

/-- Second prime of a same-bit RSA key pair. -/
public def RSAKeyPairBits.q {b : Nat} (pair : RSAKeyPairBits b) : Nat :=
  pair.val.2.val

/-- Public modulus associated with a same-bit RSA key pair. -/
public def RSAKeyPairBits.modulus {b : Nat} (pair : RSAKeyPairBits b) : Nat :=
  pair.p * pair.q

@[simp]
lemma RSAKeyPairBits.p_prime {b : Nat} (pair : RSAKeyPairBits b) :
    pair.p.Prime :=
  pair.property.1

@[simp]
lemma RSAKeyPairBits.q_prime {b : Nat} (pair : RSAKeyPairBits b) :
    pair.q.Prime :=
  pair.property.2.1

@[simp]
lemma RSAKeyPairBits.p_ne_q {b : Nat} (pair : RSAKeyPairBits b) :
    pair.p ≠ pair.q :=
  pair.property.2.2.1

@[simp]
lemma RSAKeyPairBits.p_odd {b : Nat} (pair : RSAKeyPairBits b) :
    Odd pair.p :=
  pair.property.2.2.2.1

@[simp]
lemma RSAKeyPairBits.q_odd {b : Nat} (pair : RSAKeyPairBits b) :
    Odd pair.q :=
  pair.property.2.2.2.2.1

lemma RSAKeyPairBits.p_bits {b : Nat} (pair : RSAKeyPairBits b) :
    HasExactBitLength b pair.p :=
  pair.property.2.2.2.2.2.1

lemma RSAKeyPairBits.q_bits {b : Nat} (pair : RSAKeyPairBits b) :
    HasExactBitLength b pair.q :=
  pair.property.2.2.2.2.2.2.1

lemma RSAKeyPairBits.modulus_bits {b : Nat} (pair : RSAKeyPairBits b) :
    HasExactBitLength (2 * b) pair.modulus :=
  pair.property.2.2.2.2.2.2.2

/-- Accepted independent prime pairs and the canonical RSA key carrier carry
exactly the same data. -/
def acceptedExactBitPrimePairEquiv (b : Nat) :
    AcceptedExactBitPrimePair b ≃ RSAKeyPairBits b where
  toFun pair :=
    ⟨(pair.val.1.val, pair.val.2.val),
      pair.val.1.property.1,
      pair.val.2.property.1,
      pair.property.1,
      pair.val.1.property.2.1,
      pair.val.2.property.2.1,
      pair.val.1.property.2.2,
      pair.val.2.property.2.2,
      pair.property.2⟩
  invFun pair :=
    ⟨(⟨pair.val.1, pair.p_prime, pair.p_odd, pair.p_bits⟩,
      ⟨pair.val.2, pair.q_prime, pair.q_odd, pair.q_bits⟩),
      pair.p_ne_q, pair.modulus_bits⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv pair := by
    apply Subtype.ext
    exact Prod.ext rfl rfl

/-- Any inhabited accepted-key carrier supplies an exact-width prime for each
independent draw. -/
lemma exactBitPrime_nonempty_of_keyPair {b : Nat}
    (h : Nonempty (RSAKeyPairBits b)) :
    Nonempty (ExactBitPrime b) := by
  obtain ⟨pair⟩ := h
  exact ⟨⟨pair.val.1, pair.p_prime, pair.p_odd, pair.p_bits⟩⟩

/-- Any inhabited accepted-key carrier supplies an accepted pair in the
independent product carrier. -/
lemma acceptedExactBitPrimePair_nonempty_of_keyPair {b : Nat}
    (h : Nonempty (RSAKeyPairBits b)) :
    Nonempty (AcceptedExactBitPrimePair b) :=
  Nonempty.map (acceptedExactBitPrimePairEquiv b).symm h

/-- Every ordered off-diagonal pair from the top-quarter prime set determines
an accepted exact-width RSA key pair. -/
noncomputable def topQuarterPairEmbedding {b : Nat} (hb : 512 ≤ b) :
    {pair : Nat × Nat // pair ∈ (topQuarterPrimes b).offDiag} ↪
      RSAKeyPairBits b where
  toFun pair := by
    have hp : pair.val.1 ∈ topQuarterPrimes b :=
      (Finset.mem_offDiag.mp pair.property).1
    have hq : pair.val.2 ∈ topQuarterPrimes b :=
      (Finset.mem_offDiag.mp pair.property).2.1
    have hpq : pair.val.1 ≠ pair.val.2 :=
      (Finset.mem_offDiag.mp pair.property).2.2
    have hpPrime : pair.val.1.Prime :=
      Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
    have hqPrime : pair.val.2.Prime :=
      Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hq).1
    have hpLe : pair.val.1 ≤ 2 ^ b :=
      Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
    have hqLe : pair.val.2 ≤ 2 ^ b :=
      Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hq).1
    have hpLower : 3 * 2 ^ (b - 2) < pair.val.1 := by
      by_contra h
      exact (Finset.mem_sdiff.mp hp).2
        (Nat.mem_primesLE.mpr ⟨by omega, hpPrime⟩)
    have hqLower : 3 * 2 ^ (b - 2) < pair.val.2 := by
      by_contra h
      exact (Finset.mem_sdiff.mp hq).2
        (Nat.mem_primesLE.mpr ⟨by omega, hqPrime⟩)
    have hpLt : pair.val.1 < 2 ^ b := by
      refine hpLe.lt_of_ne ?_
      intro heq
      exact Nat.Prime.not_prime_pow (by omega : 2 ≤ b) (heq ▸ hpPrime)
    have hqLt : pair.val.2 < 2 ^ b := by
      refine hqLe.lt_of_ne ?_
      intro heq
      exact Nat.Prime.not_prime_pow (by omega : 2 ≤ b) (heq ▸ hqPrime)
    have hbitPower : 2 ^ (b - 1) = 2 * 2 ^ (b - 2) := by
      rw [show b - 1 = (b - 2) + 1 by omega, pow_succ]
      omega
    have hquarterPositive : 0 < 2 ^ (b - 2) := by positivity
    have hproductPower :
        2 ^ (2 * b - 1) = 8 * (2 ^ (b - 2)) ^ 2 := by
      rw [show 2 * b - 1 = (b - 2) + (b - 2) + 3 by omega,
        pow_add, pow_add]
      ring
    have hproductLower :
        2 ^ (2 * b - 1) ≤ pair.val.1 * pair.val.2 := by
      rw [hproductPower]
      nlinarith
    have hproductUpper : pair.val.1 * pair.val.2 < 2 ^ (2 * b) := by
      calc
        pair.val.1 * pair.val.2 < 2 ^ b * 2 ^ b :=
          Nat.mul_lt_mul_of_lt_of_lt hpLt hqLt
        _ = 2 ^ (2 * b) := by rw [← pow_add]; congr 1; omega
    let pFin : Fin (2 ^ b) := ⟨pair.val.1, hpLt⟩
    let qFin : Fin (2 ^ b) := ⟨pair.val.2, hqLt⟩
    exact ⟨(pFin, qFin),
      hpPrime, hqPrime, hpq,
      hpPrime.odd_of_ne_two (by omega),
      hqPrime.odd_of_ne_two (by omega),
      ⟨by simp only [pFin]; rw [hbitPower]; omega, by simpa [pFin]⟩,
      ⟨by simp only [qFin]; rw [hbitPower]; omega, by simpa [qFin]⟩,
      ⟨hproductLower, hproductUpper⟩⟩
  inj' := by
    intro left right heq
    have hp := congrArg (fun pair : RSAKeyPairBits b => pair.val.1.val) heq
    have hq := congrArg (fun pair : RSAKeyPairBits b => pair.val.2.val) heq
    change left.val.1 = right.val.1 at hp
    change left.val.2 = right.val.2 at hq
    apply Subtype.ext
    exact Prod.ext hp hq

/-- The accepted same-bit key carrier contains every ordered distinct pair of
top-quarter primes. -/
lemma topQuarterOrderedPairCount_le_card {b : Nat} (hb : 512 ≤ b) :
    (topQuarterPrimes b).card * ((topQuarterPrimes b).card - 1) ≤
      Fintype.card (RSAKeyPairBits b) := by
  classical
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Finset.offDiag_card]
  have hcard :
      Fintype.card
          {pair : Nat × Nat // pair ∈ (topQuarterPrimes b).offDiag} ≤
        Fintype.card (RSAKeyPairBits b) :=
    Fintype.card_le_of_injective (topQuarterPairEmbedding hb)
      (topQuarterPairEmbedding hb).injective
  simpa using hcard

/-- An odd exact-`b`-bit integer lies strictly above the even lower endpoint,
so its predecessor retains the full `2^(b-1)` lower bound. -/
lemma HasExactBitLength.two_pow_le_sub_one_of_odd
    {b n : Nat} (hb : 2 ≤ b) (hbits : HasExactBitLength b n)
    (hodd : Odd n) :
    2 ^ (b - 1) ≤ n - 1 := by
  rcases hodd with ⟨k, rfl⟩
  have hpow : ∃ t, 2 ^ (b - 1) = 2 * t := by
    refine ⟨2 ^ (b - 2), ?_⟩
    rw [show b - 1 = (b - 2) + 1 by omega, pow_succ]
    omega
  rcases hpow with ⟨t, ht⟩
  have hlower := hbits.1
  omega

lemma RSAKeyPairBits.p_sub_one_lower {b : Nat}
    (pair : RSAKeyPairBits b) (hb : 2 ≤ b) :
    2 ^ (b - 1) ≤ pair.p - 1 :=
  HasExactBitLength.two_pow_le_sub_one_of_odd hb pair.p_bits pair.p_odd

lemma RSAKeyPairBits.q_sub_one_lower {b : Nat}
    (pair : RSAKeyPairBits b) (hb : 2 ≤ b) :
    2 ^ (b - 1) ≤ pair.q - 1 :=
  HasExactBitLength.two_pow_le_sub_one_of_odd hb pair.q_bits pair.q_odd

/-- Product law of two independent uniform exact-`b`-bit prime draws. -/
noncomputable def independentExactBitPrimePairs
    (b : Nat) (h : Nonempty (RSAKeyPairBits b)) :
    PMF (IndependentExactBitPrimePair b) := by
  classical
  letI : Nonempty (ExactBitPrime b) :=
    exactBitPrime_nonempty_of_keyPair h
  exact PMF.uniformOfFintype (IndependentExactBitPrimePair b)

/-- The accepted-carrier form of rejection sampling from two independent
uniform exact-width prime draws. -/
noncomputable def conditionedAcceptedPrimePairs
    (b : Nat) (h : Nonempty (RSAKeyPairBits b)) :
    PMF (AcceptedExactBitPrimePair b) := by
  classical
  letI : Nonempty (AcceptedExactBitPrimePair b) :=
    acceptedExactBitPrimePair_nonempty_of_keyPair h
  exact PMF.uniformOfFintype (AcceptedExactBitPrimePair b)

/-- The literal conditional law obtained by filtering the independent product
distribution on the accepted RSA-key event. -/
noncomputable def independentPrimePairConditioning
    (b : Nat) (h : Nonempty (RSAKeyPairBits b)) :
    PMF (IndependentExactBitPrimePair b) := by
  classical
  letI : Nonempty (ExactBitPrime b) :=
    exactBitPrime_nonempty_of_keyPair h
  let accepted : AcceptedExactBitPrimePair b :=
    Classical.choice (acceptedExactBitPrimePair_nonempty_of_keyPair h)
  have hwitness :
      ∃ pair ∈ {pair | AcceptsRSAKeyPair pair},
        pair ∈ (independentExactBitPrimePairs b h).support := by
    exact ⟨accepted.val, accepted.property, by
      simp [independentExactBitPrimePairs]⟩
  exact (independentExactBitPrimePairs b h).filter
    {pair | AcceptsRSAKeyPair pair} hwitness

private lemma filter_uniformOfFintype_apply_of_mem
    {α : Type*} [Fintype α] [Nonempty α]
    (s : Set α) [Fintype s] (_hs : Nonempty s)
    (hwitness : ∃ a ∈ s, a ∈ (PMF.uniformOfFintype α).support)
    {a : α} (ha : a ∈ s) :
    ((PMF.uniformOfFintype α).filter s hwitness) a =
      (Fintype.card s : ENNReal)⁻¹ := by
  classical
  let _ : Nonempty s := _hs
  rw [PMF.filter_apply]
  simp only [Set.indicator_of_mem ha, PMF.uniformOfFintype_apply]
  rw [← PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  have hbaseZero : (Fintype.card α : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  rw [ENNReal.inv_div
    (Or.inl (ENNReal.natCast_ne_top (Fintype.card α)))
    (Or.inl hbaseZero)]
  rw [ENNReal.div_eq_inv_mul]
  calc
    (Fintype.card α : ENNReal)⁻¹ *
          ((Fintype.card s : ENNReal)⁻¹ *
            (Fintype.card α : ENNReal)) =
        (Fintype.card s : ENNReal)⁻¹ *
          ((Fintype.card α : ENNReal)⁻¹ *
            (Fintype.card α : ENNReal)) := by ac_rfl
    _ = (Fintype.card s : ENNReal)⁻¹ := by
      rw [ENNReal.inv_mul_cancel hbaseZero
        (ENNReal.natCast_ne_top (Fintype.card α)), mul_one]

/-- Filtering the independent product law is exactly the pushforward of the
uniform accepted carrier.  This is the finite rejection-sampling equivalence,
not merely an informal description of `RSAKeyGenBits`. -/
lemma independentPrimePairConditioning_eq_conditionedAccepted_map
    (b : Nat) (h : Nonempty (RSAKeyPairBits b)) :
    independentPrimePairConditioning b h =
      (conditionedAcceptedPrimePairs b h).map Subtype.val := by
  classical
  let _ : Nonempty (ExactBitPrime b) :=
    exactBitPrime_nonempty_of_keyPair h
  let _ : Nonempty (AcceptedExactBitPrimePair b) :=
    acceptedExactBitPrimePair_nonempty_of_keyPair h
  apply PMF.ext
  intro pair
  by_cases hpair : AcceptsRSAKeyPair pair
  · rw [independentPrimePairConditioning]
    exact (filter_uniformOfFintype_apply_of_mem
      {candidate | AcceptsRSAKeyPair candidate}
      (acceptedExactBitPrimePair_nonempty_of_keyPair h)
      (by
        let accepted : AcceptedExactBitPrimePair b :=
          Classical.choice
            (acceptedExactBitPrimePair_nonempty_of_keyPair h)
        exact ⟨accepted.val, accepted.property, by
          simp⟩)
      hpair).trans (by
        rw [PMF.map_apply, tsum_eq_single
          (⟨pair, hpair⟩ : AcceptedExactBitPrimePair b)]
        · simp only [conditionedAcceptedPrimePairs,
            PMF.uniformOfFintype_apply]
          congr 1
        · intro other hne
          have hvalue : pair ≠ other.val := by
            intro heq
            apply hne
            apply Subtype.ext
            exact heq.symm
          simp [hvalue])
  · rw [independentPrimePairConditioning]
    have hnotMem :
        pair ∉ {candidate | AcceptsRSAKeyPair candidate} := hpair
    rw [PMF.filter_apply_eq_zero_of_notMem _ hnotMem]
    rw [PMF.map_apply]
    symm
    rw [ENNReal.tsum_eq_zero]
    intro accepted
    have hvalue : pair ≠ accepted.val := by
      intro heq
      exact hpair (heq ▸ accepted.property)
    simp [hvalue]

/-- Uniform theorem-side key generation on the accepted same-bit RSA key
pairs.  Nonemptiness is supplied by the effective prime-interval theorem,
never by the public factoring caller. -/
public noncomputable def RSAKeyGenBits (b : Nat) (h : Nonempty (RSAKeyPairBits b)) :
    PMF (RSAKeyPairBits b) := by
  classical
  letI : Nonempty (RSAKeyPairBits b) := h
  exact PMF.uniformOfFintype (RSAKeyPairBits b)

/-- Transporting the rejection-conditioned accepted carrier through its
canonical equivalence gives exactly the uniform RSA key generator. -/
lemma conditionedAcceptedPrimePairs_map_eq_RSAKeyGenBits
    (b : Nat) (h : Nonempty (RSAKeyPairBits b)) :
    (conditionedAcceptedPrimePairs b h).map
        (acceptedExactBitPrimePairEquiv b) =
      RSAKeyGenBits b h := by
  classical
  let _ : Nonempty (AcceptedExactBitPrimePair b) :=
    acceptedExactBitPrimePair_nonempty_of_keyPair h
  let _ : Nonempty (RSAKeyPairBits b) := h
  apply PMF.ext
  intro key
  rw [PMF.map_apply, tsum_eq_single
    ((acceptedExactBitPrimePairEquiv b).symm key)]
  · simp only [Equiv.apply_symm_apply, if_true,
      conditionedAcceptedPrimePairs, PMF.uniformOfFintype_apply,
      RSAKeyGenBits]
    rw [Fintype.card_congr (acceptedExactBitPrimePairEquiv b)]
  · intro other hne
    have hvalue : key ≠ acceptedExactBitPrimePairEquiv b other := by
      intro heq
      apply hne
      exact (acceptedExactBitPrimePairEquiv b).injective
        (by simpa using heq.symm)
    simp [hvalue]

end RSA
end QuantumAlg

end
