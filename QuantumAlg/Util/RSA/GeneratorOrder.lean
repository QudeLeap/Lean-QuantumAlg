/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.DivisorBound
import all QuantumAlg.Util.RSA.KeyGeneration
import all QuantumAlg.Util.RSA.ShortLog.Reduction
import all QuantumAlg.Util.NumberTheory.Factoring
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Effective generator-order parameters for same-bit RSA keys

This module owns only RSA arithmetic and probability thresholds.  The divisor
and prime-interval estimates used to prove them live under
`QuantumAlg.Util.NumberTheory`; the Ekerå–Håstad circuit consumes the resulting
order theorem from the algorithm layer.
-/

section

namespace QuantumAlg
namespace RSA
namespace GeneratorOrder

/-- Short-logarithm width for two `b`-bit RSA primes [EH17,
source.tex:955-977]. -/
def m (b : Nat) : Nat := b + 1

/-- Canonical source tradeoff for `s=2`, choosing the upward-rounded integer
`ell=ceil(m/2)` permitted by the requirement that `ell` be close to `m/s`
[EH17, source.tex:397-405].  The upward rounding preserves the source's
uniform lattice-obstruction bound for odd `m`. -/
def ell (b : Nat) : Nat := (b + 2) / 2

/-- Loss exponent allowed by the RSA reduction after choosing `s=2`. -/
def sourceLossBits (b : Nat) : Nat :=
  b - (b + 2) / 2 - 4

/-- Global ninth-power divisor bound rounded up to a binary exponent. -/
def divisorBoundBits (b : Nat) : Nat :=
  NumberTheory.divisorCountBoundBits b

/-- Per-coordinate cyclic-index cutoff. -/
def coordinateLossBits (b : Nat) : Nat :=
  divisorBoundBits b + b / 64

/-- Cutoff assigned to `gcd(p-1,q-1)` after the two coordinate losses. -/
public def gcdLossBits (b : Nat) : Nat :=
  sourceLossBits b - 2 * coordinateLossBits b - 4

/-- First generic width at which the deliberately conservative thresholds are
nonvacuous. -/
public def effectiveCutoffBits : Nat := 512

/-- A convenient linear upper bound for the rounded divisor exponent. -/
theorem divisorBoundBits_le (b : Nat) :
    divisorBoundBits b ≤ b / 9 + 32 := by
  unfold divisorBoundBits NumberTheory.divisorCountBoundBits
  apply (ceilDiv_le_iff_le_mul (by decide : 0 < 9)).2
  omega

/-- Above the effective cutoff, the two coordinate losses and the common
divisor loss fit strictly inside the source exponent budget. -/
theorem loss_budget_of_effective {b : Nat}
    (hb : effectiveCutoffBits ≤ b) :
    2 * coordinateLossBits b + gcdLossBits b < sourceLossBits b := by
  have hdivisor := divisorBoundBits_le b
  have hroom :
      2 * coordinateLossBits b + 4 ≤ sourceLossBits b := by
    unfold effectiveCutoffBits at hb
    unfold coordinateLossBits sourceLossBits
    omega
  unfold gcdLossBits
  omega

/-- A linear fraction of the bit width remains available for the common
divisor cutoff throughout the effective range.  This deliberately weak bound
is chosen for a transparent asymptotic proof. -/
theorem div_sixteen_le_gcdLossBits {b : Nat}
    (hb : effectiveCutoffBits ≤ b) :
    b / 16 ≤ gcdLossBits b := by
  have hdivisor := divisorBoundBits_le b
  unfold effectiveCutoffBits at hb
  unfold gcdLossBits coordinateLossBits sourceLossBits
  omega

/-- Original short-DLP order condition, before the RSA loss-exponent
simplification [EH17, source.tex:399-405]. -/
def OrderSufficient (b shortLog order : Nat) : Prop :=
  2 ^ (ell b + m b) + 2 ^ ell b * shortLog ≤ order

/-- The loss exponent and the short-DLP target exponent exactly fill the
`2*b-2` bits supplied by two odd `b`-bit prime factors. -/
theorem sourceLoss_add_targetExponent {b : Nat} (hb : 9 ≤ b) :
    sourceLossBits b + (ell b + m b + 1) = 2 * (b - 1) := by
  unfold sourceLossBits ell m
  have hhalf : (b + 2) / 2 + 4 ≤ b := by omega
  omega

/-- Deterministic arithmetic core of the effective generator-order gate.

Each CRT coordinate may lose `coordinateLossBits b` bits relative to its
prime-order unit group, and their common divisor may lose a further
`gcdLossBits b` bits.  If the combined loss stays below the source budget,
the resulting LCM satisfies the original Ekerå–Håstad short-DLP order
condition.  Probability bounds for the three excluded events are proved
separately; this theorem contains no distributional assumption. -/
theorem effectiveOrderCondition
    {b p q shortLog leftOrder rightOrder : Nat}
    (hb : 9 ≤ b)
    (hpLower : 2 ^ (b - 1) ≤ p - 1)
    (hqLower : 2 ^ (b - 1) ≤ q - 1)
    (hshortLog : shortLog < 2 ^ m b)
    (hleft :
      (p - 1) / 2 ^ coordinateLossBits b < leftOrder)
    (hright :
      (q - 1) / 2 ^ coordinateLossBits b < rightOrder)
    (hcommon : Nat.gcd leftOrder rightOrder < 2 ^ gcdLossBits b)
    (hloss :
      2 * coordinateLossBits b + gcdLossBits b < sourceLossBits b) :
    OrderSufficient b shortLog (Nat.lcm leftOrder rightOrder) := by
  have hcoordinatePos : 0 < 2 ^ coordinateLossBits b := by positivity
  have hleftMul :
      p - 1 < 2 ^ coordinateLossBits b * leftOrder := by
    have := (Nat.div_lt_iff_lt_mul hcoordinatePos).mp hleft
    simpa [Nat.mul_comm] using this
  have hrightMul :
      q - 1 < 2 ^ coordinateLossBits b * rightOrder := by
    have := (Nat.div_lt_iff_lt_mul hcoordinatePos).mp hright
    simpa [Nat.mul_comm] using this
  have hleftPos : 0 < leftOrder :=
    lt_of_le_of_lt (Nat.zero_le _) hleft
  have hrightPos : 0 < rightOrder :=
    lt_of_le_of_lt (Nat.zero_le _) hright
  have hlcmPos : 0 < Nat.lcm leftOrder rightOrder :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hleftPos.ne' hrightPos.ne')
  have hphiToProduct :
      (p - 1) * (q - 1) <
        2 ^ (2 * coordinateLossBits b) * (leftOrder * rightOrder) := by
    have hproduct := Nat.mul_lt_mul_of_lt_of_lt hleftMul hrightMul
    simpa [pow_add, two_mul, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hproduct
  have hproductToLcm :
      leftOrder * rightOrder <
        2 ^ gcdLossBits b * Nat.lcm leftOrder rightOrder := by
    have hscaled :=
      Nat.mul_lt_mul_of_pos_right hcommon hlcmPos
    rw [Nat.gcd_mul_lcm] at hscaled
    simpa [Nat.mul_comm] using hscaled
  have hphiToUsedLoss :
      (p - 1) * (q - 1) <
        2 ^ (2 * coordinateLossBits b + gcdLossBits b) *
          Nat.lcm leftOrder rightOrder := by
    calc
      (p - 1) * (q - 1) <
          2 ^ (2 * coordinateLossBits b) * (leftOrder * rightOrder) :=
        hphiToProduct
      _ < 2 ^ (2 * coordinateLossBits b) *
          (2 ^ gcdLossBits b * Nat.lcm leftOrder rightOrder) :=
        Nat.mul_lt_mul_of_pos_left hproductToLcm (by positivity)
      _ = 2 ^ (2 * coordinateLossBits b + gcdLossBits b) *
          Nat.lcm leftOrder rightOrder := by
        rw [pow_add]
        ac_rfl
  have husedPow :
      2 ^ (2 * coordinateLossBits b + gcdLossBits b) ≤
        2 ^ sourceLossBits b :=
    Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hloss)
  have hphiToSourceLoss :
      (p - 1) * (q - 1) <
        2 ^ sourceLossBits b * Nat.lcm leftOrder rightOrder :=
    hphiToUsedLoss.trans_le (Nat.mul_le_mul_right _ husedPow)
  have hphiLower :
      2 ^ (2 * (b - 1)) ≤ (p - 1) * (q - 1) := by
    simpa [pow_add, two_mul] using Nat.mul_le_mul hpLower hqLower
  have htargetScaled :
      2 ^ sourceLossBits b * 2 ^ (ell b + m b + 1) <
        2 ^ sourceLossBits b * Nat.lcm leftOrder rightOrder := by
    rw [← pow_add, sourceLoss_add_targetExponent hb]
    exact hphiLower.trans_lt hphiToSourceLoss
  have htarget :
      2 ^ (ell b + m b + 1) < Nat.lcm leftOrder rightOrder :=
    (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ sourceLossBits b)).mp
      htargetScaled
  have hshortScaled :
      2 ^ ell b * shortLog < 2 ^ (ell b + m b) := by
    simpa [pow_add] using
      Nat.mul_lt_mul_of_pos_left hshortLog (by positivity : 0 < 2 ^ ell b)
  unfold OrderSufficient
  have hsum :
      2 ^ (ell b + m b) + 2 ^ ell b * shortLog <
        2 ^ (ell b + m b + 1) := by
    calc
      2 ^ (ell b + m b) + 2 ^ ell b * shortLog <
          2 ^ (ell b + m b) + 2 ^ (ell b + m b) :=
        Nat.add_lt_add_left hshortScaled _
      _ = 2 ^ (ell b + m b + 1) := by
        rw [pow_succ]
        omega
  exact Nat.le_of_lt (hsum.trans htarget)

/-- The hidden RSA short logarithm of an exact same-bit key fits the source
register width `m=b+1`. -/
theorem RSAKeyPairBits.shortLogSecret_lt_two_pow_m {b : Nat}
    (pair : RSAKeyPairBits b) :
    shortLogSecret pair.p pair.q < 2 ^ m b := by
  have hpUpper := pair.p_bits.2
  have hqUpper := pair.q_bits.2
  unfold shortLogSecret m
  rw [pow_succ]
  omega

/-- Canonical CRT equivalence attached to one same-bit RSA key. -/
noncomputable def componentEquiv {b : Nat} (pair : RSAKeyPairBits b) :
    (ZMod pair.modulus)ˣ ≃* (ZMod pair.p)ˣ × (ZMod pair.q)ˣ :=
  NumberTheory.Factoring.RandomBaseUnitSample.crtComponentEquiv <|
    NumberTheory.Factoring.SemiprimeFactorModel.ofDistinctPrimes
      pair.p_prime pair.q_prime pair.p_ne_q

/-- The two CRT components of one actual public-unit sample. -/
noncomputable def components {b : Nat} (pair : RSAKeyPairBits b)
    (unit : (ZMod pair.modulus)ˣ) : (ZMod pair.p)ˣ × (ZMod pair.q)ˣ :=
  componentEquiv pair unit

/-- Orders of the two CRT components of one actual public-unit sample. -/
noncomputable def componentOrders {b : Nat} (pair : RSAKeyPairBits b)
    (unit : (ZMod pair.modulus)ˣ) : Nat × Nat :=
  (orderOf (components pair unit).1, orderOf (components pair unit).2)

/-- The common divisor of the sampled CRT component orders is bounded by the
common divisor of the two full prime-group orders. -/
theorem componentOrderGcd_le_keyGcd {b : Nat}
    (pair : RSAKeyPairBits b) (unit : (ZMod pair.modulus)ˣ) :
    Nat.gcd (componentOrders pair unit).1 (componentOrders pair unit).2 ≤
      Nat.gcd (pair.p - 1) (pair.q - 1) := by
  let _ : NeZero pair.p := ⟨pair.p_prime.ne_zero⟩
  let _ : NeZero pair.q := ⟨pair.q_prime.ne_zero⟩
  let _ : Fact pair.p.Prime := ⟨pair.p_prime⟩
  let _ : Fact pair.q.Prime := ⟨pair.q_prime⟩
  have hleft : (componentOrders pair unit).1 ∣ pair.p - 1 := by
    change orderOf (components pair unit).1 ∣ pair.p - 1
    rw [← ZMod.card_units]
    exact orderOf_dvd_card
  have hright : (componentOrders pair unit).2 ∣ pair.q - 1 := by
    change orderOf (components pair unit).2 ∣ pair.q - 1
    rw [← ZMod.card_units]
    exact orderOf_dvd_card
  have hkeyGcdPos : 0 < Nat.gcd (pair.p - 1) (pair.q - 1) :=
    Nat.gcd_pos_of_pos_left _ (by
      have := pair.p_prime.one_lt
      omega)
  exact Nat.le_of_dvd hkeyGcdPos (gcd_dvd_gcd hleft hright)

/-- The global order of an actual RSA unit is the LCM of its two recorded CRT
component orders. -/
theorem orderOf_eq_lcm_componentOrders {b : Nat}
    (pair : RSAKeyPairBits b) (unit : (ZMod pair.modulus)ˣ) :
    orderOf unit =
      Nat.lcm (componentOrders pair unit).1 (componentOrders pair unit).2 := by
  let model := NumberTheory.Factoring.SemiprimeFactorModel.ofDistinctPrimes
    pair.p_prime pair.q_prime pair.p_ne_q
  let sample := NumberTheory.Factoring.RandomBaseUnitSample.ofUnit
    (model := model) unit
  convert
    NumberTheory.Factoring.RandomBaseUnitSample.orderOf_eq_lcm_crtComponentPair sample
      using 1 <;>
    rfl

/-- Actual same-bit RSA specialization of `effectiveOrderCondition`.  The
hypotheses are precisely the complements of the two coordinate low-order
events and the common-divisor tail event. -/
theorem sampledUnit_orderSufficient
    {b : Nat} (pair : RSAKeyPairBits b)
    (unit : (ZMod pair.modulus)ˣ)
    (hb : 9 ≤ b)
    (hleft :
      (pair.p - 1) / 2 ^ coordinateLossBits b <
        (componentOrders pair unit).1)
    (hright :
      (pair.q - 1) / 2 ^ coordinateLossBits b <
        (componentOrders pair unit).2)
    (hcommon :
      Nat.gcd (componentOrders pair unit).1
          (componentOrders pair unit).2 <
        2 ^ gcdLossBits b)
    (hloss :
      2 * coordinateLossBits b + gcdLossBits b < sourceLossBits b) :
    OrderSufficient b (shortLogSecret pair.p pair.q) (orderOf unit) := by
  rw [orderOf_eq_lcm_componentOrders pair unit]
  exact effectiveOrderCondition hb
    (pair.p_sub_one_lower (by omega))
    (pair.q_sub_one_lower (by omega))
    (RSAKeyPairBits.shortLogSecret_lt_two_pow_m pair)
    hleft hright hcommon hloss

theorem rsa1024_parameters :
    m 1024 = 1025 ∧ ell 1024 = 513 ∧ sourceLossBits 1024 = 507 := by
  decide

theorem rsa1024_loss_thresholds :
    divisorBoundBits 1024 = 145 ∧
      coordinateLossBits 1024 = 161 ∧
      gcdLossBits 1024 = 181 := by
  decide

/-- The two cyclic-coordinate cutoffs plus the common-factor cutoff fit below
the source loss threshold with four bits of margin. -/
theorem rsa1024_loss_certificate :
    2 * coordinateLossBits 1024 + gcdLossBits 1024 = 503 ∧
      2 * coordinateLossBits 1024 + gcdLossBits 1024 <
        sourceLossBits 1024 := by
  decide

/-- Same-bit RSA keys whose two group orders share a divisor at least `D`.
This is the key-generation event excluded by the common-factor part of the
effective generator-order analysis. -/
noncomputable def commonDivisorBadKeys (b D : Nat) :
    Finset (RSAKeyPairBits b) :=
  Finset.univ.filter fun pair =>
    D ≤ Nat.gcd (pair.p - 1) (pair.q - 1)

/-- Forget primality and retain only the two positive predecessors.  This
embeds every bad RSA key into the larger all-integer common-divisor event, so
the analytic numerator bound never needs primes in arithmetic progressions. -/
noncomputable def commonDivisorBadKeyEmbedding (b D : Nat) :
    {pair : RSAKeyPairBits b // pair ∈ commonDivisorBadKeys b D} ↪
      {pair : Nat × Nat //
        pair ∈ NumberTheory.commonDivisorPairs (2 ^ b) D} where
  toFun pair := by
    have hbad :
        D ≤ Nat.gcd (pair.val.p - 1) (pair.val.q - 1) := by
      exact (Finset.mem_filter.mp pair.property).2
    exact ⟨(pair.val.p - 1, pair.val.q - 1),
      NumberTheory.mem_commonDivisorPairs
        (by have := pair.val.p_prime.one_lt; omega)
        (by have := pair.val.q_prime.one_lt; omega)
        (by have := pair.val.p_bits.2; omega)
        (by have := pair.val.q_bits.2; omega)
        hbad⟩
  inj' := by
    intro left right heq
    have hpSub := congrArg
      (fun pair : {pair : Nat × Nat //
        pair ∈ NumberTheory.commonDivisorPairs (2 ^ b) D} => pair.val.1) heq
    have hqSub := congrArg
      (fun pair : {pair : Nat × Nat //
        pair ∈ NumberTheory.commonDivisorPairs (2 ^ b) D} => pair.val.2) heq
    have hp : left.val.p = right.val.p := by
      have hleft := left.val.p_prime.one_lt
      have hright := right.val.p_prime.one_lt
      dsimp only at hpSub
      omega
    have hq : left.val.q = right.val.q := by
      have hleft := left.val.q_prime.one_lt
      have hright := right.val.q_prime.one_lt
      dsimp only at hqSub
      omega
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (Fin.ext hp) (Fin.ext hq)

/-- The all-integer common-divisor union is an upper bound for the number of
bad accepted RSA keys. -/
theorem commonDivisorBadKeys_card_le (b D : Nat) :
    (commonDivisorBadKeys b D).card ≤
      (NumberTheory.commonDivisorPairs (2 ^ b) D).card := by
  classical
  exact Finset.card_le_card_of_injective
    (commonDivisorBadKeyEmbedding b D).injective

/-- Explicit real-valued numerator bound for the common-divisor bad-key
event.  Counting all positive integers makes this conservative but fully
elementary. -/
theorem commonDivisorBadKeys_card_bound (b D : Nat) (hD : 0 < D) :
    (D : Real) * (commonDivisorBadKeys b D).card ≤
      2 * ((2 ^ b : Nat) : Real) ^ 2 := by
  have hcardNat := commonDivisorBadKeys_card_le b D
  have hcardReal :
      ((commonDivisorBadKeys b D).card : Real) ≤
        ((NumberTheory.commonDivisorPairs (2 ^ b) D).card : Real) := by
    exact_mod_cast hcardNat
  calc
    (D : Real) * (commonDivisorBadKeys b D).card ≤
        (D : Real) *
          (NumberTheory.commonDivisorPairs (2 ^ b) D).card :=
      mul_le_mul_of_nonneg_left hcardReal (by positivity)
    _ ≤ 2 * ((2 ^ b : Nat) : Real) ^ 2 :=
      NumberTheory.commonDivisorPairs_card_bound (2 ^ b) D
        (by positivity) hD

/-- Conservative key-generation failure bound obtained by cancelling the
ambient `2^(2b)` scale against the top-quarter-prime denominator. -/
noncomputable def keyFailureBound (b : Nat) : Real :=
  4096 * (b : Real) ^ 2 / ((2 ^ gcdLossBits b : Nat) : Real)

/-- Exact uniform-keygen mass of the common-divisor exceptional event. -/
noncomputable def keyGenerationBadFraction (b : Nat) : Real :=
  ((commonDivisorBadKeys b (2 ^ gcdLossBits b)).card : Real) /
    Fintype.card (RSAKeyPairBits b)

/-- The exact common-divisor exceptional fraction is the actual event mass of
the canonical uniform same-bit RSA key generator. -/
theorem RSAKeyGenBits_commonDivisorBadMass_eq (b : Nat)
    (h : Nonempty (RSAKeyPairBits b)) :
    (RSAKeyGenBits b h).toOuterMeasure
        {pair | 2 ^ gcdLossBits b ≤
          Nat.gcd (pair.p - 1) (pair.q - 1)} =
      ENNReal.ofReal (keyGenerationBadFraction b) := by
  classical
  let _ : Nonempty (RSAKeyPairBits b) := h
  rw [RSAKeyGenBits, PMF.toOuterMeasure_uniformOfFintype_apply]
  unfold keyGenerationBadFraction
  rw [ENNReal.ofReal_div_of_pos (by
    exact_mod_cast Fintype.card_pos_iff.mpr h)]
  simp only [ENNReal.ofReal_natCast]
  congr 1
  rw [Fintype.card_subtype]
  rfl

/-- The analytic key failure bound really dominates the exact bad-key mass of
the canonical uniform same-bit distribution. -/
theorem keyGenerationBadFraction_le_keyFailureBound {b : Nat}
    (hb : effectiveCutoffBits ≤ b) :
    keyGenerationBadFraction b ≤ keyFailureBound b := by
  let lower := NumberTheory.topQuarterPrimeCountLowerBound b
  let total := Fintype.card (RSAKeyPairBits b)
  let bad := (commonDivisorBadKeys b (2 ^ gcdLossBits b)).card
  have hlowerTwo : 2 ≤ lower := by
    exact two_le_topQuarterPrimeCountLowerBound hb
  have hlowerCard : lower ≤ (topQuarterPrimes b).card := by
    exact topQuarterPrimeCountLowerBound_le_card hb
  have hlowerProduct : lower * (lower - 1) ≤
      (topQuarterPrimes b).card * ((topQuarterPrimes b).card - 1) :=
    Nat.mul_le_mul hlowerCard (Nat.sub_le_sub_right hlowerCard 1)
  have hlowerTotal : lower * (lower - 1) ≤ total := by
    exact hlowerProduct.trans (topQuarterOrderedPairCount_le_card hb)
  have htotalPos : 0 < total := by
    exact Fintype.card_pos_iff.mpr (rsaKeyPairBits_nonempty hb)
  have hpower : 2 ^ b ≤ 2 * (16 * b) * lower := by
    exact power_le_twice_denominator_mul_topQuarterLowerBound hb
  have hpowerReal : ((2 ^ b : Nat) : Real) ≤
      32 * (b : Real) * (lower : Real) := by
    have hcast : ((2 ^ b : Nat) : Real) ≤
        ((2 * (16 * b) * lower : Nat) : Real) := by
      exact_mod_cast hpower
    calc
      ((2 ^ b : Nat) : Real) ≤
          ((2 * (16 * b) * lower : Nat) : Real) := hcast
      _ = 32 * (b : Real) * (lower : Real) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hpowerSq : (((2 ^ b : Nat) : Real) ^ 2) ≤
      (32 * (b : Real) * (lower : Real)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hpowerReal 2
  have hlowerTotalReal :
      (lower : Real) * ((lower - 1 : Nat) : Real) ≤ (total : Real) := by
    exact_mod_cast hlowerTotal
  have hlowerSubCast : ((lower - 1 : Nat) : Real) = lower - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ lower)]
    norm_num
  have hlowerSq : (lower : Real) ^ 2 ≤ 2 * (total : Real) := by
    rw [hlowerSubCast] at hlowerTotalReal
    have hlowerReal : (2 : Real) ≤ lower := by exact_mod_cast hlowerTwo
    have hfactor :
        0 ≤ (lower : Real) * ((lower : Real) - 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hlowerReal)
    have hlowerLeProduct :
        (lower : Real) ≤ (lower : Real) * ((lower : Real) - 1) := by
      nlinarith
    nlinarith
  have hscaledLower :
      2048 * (b : Real) ^ 2 * (lower : Real) ^ 2 ≤
        4096 * (b : Real) ^ 2 * (total : Real) := by
    have := mul_le_mul_of_nonneg_left hlowerSq
      (show 0 ≤ 2048 * (b : Real) ^ 2 by positivity)
    calc
      2048 * (b : Real) ^ 2 * (lower : Real) ^ 2 ≤
          (2048 * (b : Real) ^ 2) * (2 * (total : Real)) := by
        simpa [mul_assoc] using this
      _ = 4096 * (b : Real) ^ 2 * (total : Real) := by ring
  have hambient :
      2 * (((2 ^ b : Nat) : Real) ^ 2) ≤
        4096 * (b : Real) ^ 2 * (total : Real) := by
    calc
      2 * (((2 ^ b : Nat) : Real) ^ 2) ≤
          2 * (32 * (b : Real) * (lower : Real)) ^ 2 :=
        mul_le_mul_of_nonneg_left hpowerSq (by norm_num)
      _ = 2048 * (b : Real) ^ 2 * (lower : Real) ^ 2 := by ring
      _ ≤ 4096 * (b : Real) ^ 2 * (total : Real) := hscaledLower
  have hbad :
      (((2 ^ gcdLossBits b : Nat) : Real) * (bad : Real)) ≤
        2 * (((2 ^ b : Nat) : Real) ^ 2) := by
    exact commonDivisorBadKeys_card_bound b (2 ^ gcdLossBits b)
      (by positivity)
  have hweighted :
      ((2 ^ gcdLossBits b : Nat) : Real) * (bad : Real) ≤
        4096 * (b : Real) ^ 2 * (total : Real) :=
    hbad.trans hambient
  have htotalRealPos : (0 : Real) < total := by exact_mod_cast htotalPos
  have hcutoffRealPos : (0 : Real) < (2 ^ gcdLossBits b : Nat) := by
    positivity
  unfold keyGenerationBadFraction keyFailureBound
  change (bad : Real) / (total : Real) ≤
    4096 * (b : Real) ^ 2 /
      ((2 ^ gcdLossBits b : Nat) : Real)
  apply (div_le_div_iff₀ htotalRealPos hcutoffRealPos).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hweighted

/-- Uniform-generator failure bound for the two cyclic CRT coordinates. -/
noncomputable def generatorFailureBound (b : Nat) : Real :=
  2 / ((2 ^ (b / 64) : Nat) : Real)

/-- Above the effective cutoff, the two-coordinate generator tail is at most
`1/128`. -/
theorem generatorFailureBound_le_oneOver128 {b : Nat}
    (hb : effectiveCutoffBits ≤ b) :
    generatorFailureBound b ≤ (1 / 128 : Real) := by
  have hexponent : 8 ≤ b / 64 := by
    unfold effectiveCutoffBits at hb
    omega
  have hpowNat : 2 ^ 8 ≤ 2 ^ (b / 64) :=
    Nat.pow_le_pow_right (by decide) hexponent
  have hpowReal : (2 : Real) ^ 8 ≤ (2 : Real) ^ (b / 64) := by
    exact_mod_cast hpowNat
  unfold generatorFailureBound
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    2 / (2 : Real) ^ (b / 64) ≤ 2 / (2 : Real) ^ 8 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hpowReal
    _ = 1 / 128 := by norm_num

/-- Total RSA key/generator exceptional mass used by the effective
Ekerå–Håstad order gate. -/
noncomputable def effectiveFailure (b : Nat) : Real :=
  keyFailureBound b + generatorFailureBound b

theorem effectiveFailure_nonneg (b : Nat) : 0 ≤ effectiveFailure b := by
  unfold effectiveFailure keyFailureBound generatorFailureBound
  positivity

theorem keyFailureBound_nonneg (b : Nat) : 0 ≤ keyFailureBound b := by
  unfold keyFailureBound
  positivity

/-- The explicit key/generator exceptional-mass bound vanishes with the prime
bit width.  The proof uses only the elementary common-divisor count, the
top-quarter prime count, and exponential domination of a quadratic. -/
theorem effectiveFailure_tendsto_zero :
    Filter.Tendsto effectiveFailure Filter.atTop (nhds 0) := by
  let envelope : Nat → Real := fun b =>
    4194304 * (((b / 16 : Nat) : Real) ^ 2) /
      (2 : Real) ^ (b / 16)
  have hbase :
      Filter.Tendsto (fun n : Nat => (n : Real) ^ 2 / (2 : Real) ^ n)
        Filter.atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have henvelopeIndex :
      Filter.Tendsto
        (fun n : Nat =>
          4194304 * ((n : Real) ^ 2) / (2 : Real) ^ n)
        Filter.atTop (nhds 0) := by
    convert hbase.const_mul (4194304 : Real) using 1
    · ext n
      ring
    · norm_num
  have henvelope :
      Filter.Tendsto envelope Filter.atTop (nhds 0) := by
    exact henvelopeIndex.comp
      (Nat.tendsto_div_const_atTop (by norm_num : (16 : Nat) ≠ 0))
  have hkeyLe : ∀ᶠ b in Filter.atTop, keyFailureBound b ≤ envelope b := by
    apply Filter.eventually_atTop.2
    refine ⟨effectiveCutoffBits, fun b hb => ?_⟩
    have hgcd := div_sixteen_le_gcdLossBits hb
    have hpowNat : 2 ^ (b / 16) ≤ 2 ^ gcdLossBits b :=
      Nat.pow_le_pow_right (by decide) hgcd
    have hpowReal : (2 : Real) ^ (b / 16) ≤
        (2 : Real) ^ gcdLossBits b := by
      exact_mod_cast hpowNat
    have hbNat : b ≤ 32 * (b / 16) := by
      unfold effectiveCutoffBits at hb
      omega
    have hbReal : (b : Real) ≤
        32 * ((b / 16 : Nat) : Real) := by
      exact_mod_cast hbNat
    have hsq : (b : Real) ^ 2 ≤
        (32 * ((b / 16 : Nat) : Real)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbReal 2
    have hnum : 4096 * (b : Real) ^ 2 ≤
        4194304 * (((b / 16 : Nat) : Real) ^ 2) := by
      calc
        4096 * (b : Real) ^ 2 ≤
            4096 * (32 * ((b / 16 : Nat) : Real)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = 4194304 * (((b / 16 : Nat) : Real) ^ 2) := by
          ring
    unfold keyFailureBound envelope
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    calc
      4096 * (b : Real) ^ 2 / (2 : Real) ^ gcdLossBits b ≤
          4096 * (b : Real) ^ 2 / (2 : Real) ^ (b / 16) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpowReal
      _ ≤ 4194304 * (((b / 16 : Nat) : Real) ^ 2) /
          (2 : Real) ^ (b / 16) :=
        div_le_div_of_nonneg_right hnum (by positivity)
  have hkey :
      Filter.Tendsto keyFailureBound Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall keyFailureBound_nonneg)
      hkeyLe henvelope
  have hgenerator :
      Filter.Tendsto generatorFailureBound Filter.atTop (nhds 0) := by
    have hpow :
        Filter.Tendsto (fun n : Nat => (1 / 2 : Real) ^ n)
          Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hcomposed := hpow.comp
      (Nat.tendsto_div_const_atTop (by norm_num : (64 : Nat) ≠ 0))
    convert hcomposed.const_mul (2 : Real) using 1
    · ext b
      unfold generatorFailureBound
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num
    · norm_num
  change Filter.Tendsto
    (fun b => keyFailureBound b + generatorFailureBound b)
      Filter.atTop (nhds 0)
  simpa only [add_zero] using hkey.add hgenerator

/-- The key-generation component alone vanishes with the prime bit width. -/
theorem keyFailureBound_tendsto_zero :
    Filter.Tendsto keyFailureBound Filter.atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall keyFailureBound_nonneg)
    (Filter.Eventually.of_forall fun b => ?_)
    effectiveFailure_tendsto_zero
  unfold effectiveFailure
  exact le_add_of_nonneg_right (by
    unfold generatorFailureBound
    positivity)

/-- At 1024-bit prime width, the complete key/generator exceptional mass is
strictly below `1/30000`. -/
theorem rsa1024_generator_failure_lt :
    effectiveFailure 1024 < (1 / 30000 : Real) := by
  rw [effectiveFailure, keyFailureBound, generatorFailureBound,
    rsa1024_loss_thresholds.2.2]
  norm_num

/-- The generic divisor-count theorem specialized to the binary budget used
by the RSA generator-order analysis. -/
theorem card_divisors_lt_two_pow_divisorBoundBits
    {n b : Nat} (hn : n ≠ 0) (hnLt : n < 2 ^ b) :
    n.divisors.card < 2 ^ divisorBoundBits b :=
  NumberTheory.card_divisors_lt_two_pow_divisorCountBoundBits hn hnLt

/-- For a prime below `2^b`, a uniformly chosen nonzero residue has order at
most the indexed cutoff with frequency strictly below `2^(-tailBits)`. -/
theorem primeUnits_lowOrder_tail
    {p b tailBits : Nat} [Fact p.Prime] (hpLt : p < 2 ^ b) :
    2 ^ tailBits *
        (Finset.univ.filter fun unit : (ZMod p)ˣ =>
          orderOf unit ≤ Fintype.card (ZMod p)ˣ /
            2 ^ (divisorBoundBits b + tailBits)).card <
      Fintype.card (ZMod p)ˣ := by
  have hp : p.Prime := Fact.out
  let _ : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  apply NumberTheory.pow_tail_mul_card_lowOrder_lt_card
  apply card_divisors_lt_two_pow_divisorBoundBits
  · exact Fintype.card_ne_zero
  · rw [ZMod.card_units]
    exact (Nat.sub_le p 1).trans_lt hpLt

/-- Union bound for the two cyclic CRT coordinates.  Under the uniform
product carrier, the fraction of pairs for which either coordinate loses more
than the prescribed index bits is strictly below `2 * 2^(-tailBits)`. -/
theorem primeUnitPairs_lowOrder_tail
    {p q b tailBits : Nat} [Fact p.Prime] [Fact q.Prime]
    (hpLt : p < 2 ^ b) (hqLt : q < 2 ^ b) :
    2 ^ tailBits *
        (Finset.univ.filter fun pair : (ZMod p)ˣ × (ZMod q)ˣ =>
          orderOf pair.1 ≤ Fintype.card (ZMod p)ˣ /
              2 ^ (divisorBoundBits b + tailBits) ∨
            orderOf pair.2 ≤ Fintype.card (ZMod q)ˣ /
              2 ^ (divisorBoundBits b + tailBits)).card <
      2 * Fintype.card ((ZMod p)ˣ × (ZMod q)ˣ) := by
  classical
  let leftBad : Finset (ZMod p)ˣ :=
    Finset.univ.filter fun unit =>
      orderOf unit ≤ Fintype.card (ZMod p)ˣ /
        2 ^ (divisorBoundBits b + tailBits)
  let rightBad : Finset (ZMod q)ˣ :=
    Finset.univ.filter fun unit =>
      orderOf unit ≤ Fintype.card (ZMod q)ˣ /
        2 ^ (divisorBoundBits b + tailBits)
  let badPairs : Finset ((ZMod p)ˣ × (ZMod q)ˣ) :=
    Finset.univ.filter fun pair => pair.1 ∈ leftBad ∨ pair.2 ∈ rightBad
  have hsubset :
      badPairs ⊆
        (leftBad.product (Finset.univ : Finset (ZMod q)ˣ)) ∪
          ((Finset.univ : Finset (ZMod p)ˣ).product rightBad) := by
    intro pair hpair
    simp only [badPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hpair
    rcases hpair with hleft | hright
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hleft,
        Finset.mem_univ _⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨
        Finset.mem_univ _, hright⟩)
  have hcard :
      badPairs.card ≤
        leftBad.card * Fintype.card (ZMod q)ˣ +
          Fintype.card (ZMod p)ˣ * rightBad.card := by
    calc
      badPairs.card ≤
          ((leftBad.product (Finset.univ : Finset (ZMod q)ˣ)) ∪
            ((Finset.univ : Finset (ZMod p)ˣ).product rightBad)).card :=
        Finset.card_le_card hsubset
      _ ≤ (leftBad.product (Finset.univ : Finset (ZMod q)ˣ)).card +
          ((Finset.univ : Finset (ZMod p)ˣ).product rightBad).card :=
        Finset.card_union_le _ _
      _ = leftBad.card * Fintype.card (ZMod q)ˣ +
          Fintype.card (ZMod p)ˣ * rightBad.card := by simp
  have hleft :
      2 ^ tailBits * leftBad.card < Fintype.card (ZMod p)ˣ := by
    simpa [leftBad] using
      primeUnits_lowOrder_tail (p := p) (b := b)
        (tailBits := tailBits) hpLt
  have hright :
      2 ^ tailBits * rightBad.card < Fintype.card (ZMod q)ˣ := by
    simpa [rightBad] using
      primeUnits_lowOrder_tail (p := q) (b := b)
        (tailBits := tailBits) hqLt
  have hleftScaled :
      (2 ^ tailBits * leftBad.card) * Fintype.card (ZMod q)ˣ <
        Fintype.card (ZMod p)ˣ * Fintype.card (ZMod q)ˣ :=
    Nat.mul_lt_mul_of_pos_right hleft Fintype.card_pos
  have hrightScaled :
      Fintype.card (ZMod p)ˣ * (2 ^ tailBits * rightBad.card) <
        Fintype.card (ZMod p)ˣ * Fintype.card (ZMod q)ˣ :=
    Nat.mul_lt_mul_of_pos_left hright Fintype.card_pos
  have hweighted :
      2 ^ tailBits * badPairs.card <
        2 * (Fintype.card (ZMod p)ˣ * Fintype.card (ZMod q)ˣ) := by
    calc
      2 ^ tailBits * badPairs.card ≤
          2 ^ tailBits *
            (leftBad.card * Fintype.card (ZMod q)ˣ +
              Fintype.card (ZMod p)ˣ * rightBad.card) :=
        Nat.mul_le_mul_left _ hcard
      _ = (2 ^ tailBits * leftBad.card) * Fintype.card (ZMod q)ˣ +
          Fintype.card (ZMod p)ˣ * (2 ^ tailBits * rightBad.card) := by
        rw [Nat.mul_add]
        ac_rfl
      _ < Fintype.card (ZMod p)ˣ * Fintype.card (ZMod q)ˣ +
          Fintype.card (ZMod p)ˣ * Fintype.card (ZMod q)ˣ :=
        Nat.add_lt_add hleftScaled hrightScaled
      _ = 2 * (Fintype.card (ZMod p)ˣ * Fintype.card (ZMod q)ˣ) := by
        omega
  simpa [badPairs, leftBad, rightBad, Fintype.card_prod] using hweighted

/-- Transport the uniform-product coordinate tail through the actual CRT
equivalence of one same-bit RSA key. -/
theorem sampledUnit_lowOrder_tail
    {b tailBits : Nat} (pair : RSAKeyPairBits b)
    [NeZero pair.p] [NeZero pair.q] [NeZero pair.modulus] :
    2 ^ tailBits *
        (Finset.univ.filter fun unit : (ZMod pair.modulus)ˣ =>
          (componentOrders pair unit).1 ≤
              Fintype.card (ZMod pair.p)ˣ /
                2 ^ (divisorBoundBits b + tailBits) ∨
            (componentOrders pair unit).2 ≤
              Fintype.card (ZMod pair.q)ˣ /
                2 ^ (divisorBoundBits b + tailBits)).card <
      2 * Fintype.card (ZMod pair.modulus)ˣ := by
  classical
  let _ : Fact pair.p.Prime := ⟨pair.p_prime⟩
  let _ : Fact pair.q.Prime := ⟨pair.q_prime⟩
  let productBad : (ZMod pair.p)ˣ × (ZMod pair.q)ˣ → Prop :=
    fun components =>
      orderOf components.1 ≤ Fintype.card (ZMod pair.p)ˣ /
          2 ^ (divisorBoundBits b + tailBits) ∨
        orderOf components.2 ≤ Fintype.card (ZMod pair.q)ˣ /
          2 ^ (divisorBoundBits b + tailBits)
  let unitBad : (ZMod pair.modulus)ˣ → Prop :=
    fun unit => productBad (componentEquiv pair unit)
  have hcard :
      (Finset.univ.filter unitBad).card =
        (Finset.univ.filter productBad).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr <|
      (componentEquiv pair).toEquiv.subtypeEquiv fun _ => Iff.rfl
  have htotal :
      Fintype.card (ZMod pair.modulus)ˣ =
        Fintype.card ((ZMod pair.p)ˣ × (ZMod pair.q)ˣ) :=
    Fintype.card_congr (componentEquiv pair).toEquiv
  have hproduct := primeUnitPairs_lowOrder_tail
    (p := pair.p) (q := pair.q) (b := b) (tailBits := tailBits)
    pair.p_bits.2 pair.q_bits.2
  change 2 ^ tailBits * (Finset.univ.filter unitBad).card <
    2 * Fintype.card (ZMod pair.modulus)ˣ
  rw [hcard, htotal]
  simpa [productBad] using hproduct

/-- A public RSA unit is exceptional when either CRT coordinate has order at
most the selected indexed cutoff. -/
def CoordinateOrderBad {b : Nat} (pair : RSAKeyPairBits b)
    (tailBits : Nat) (unit : (ZMod pair.modulus)ˣ) : Prop :=
  (componentOrders pair unit).1 ≤
      (pair.p - 1) / 2 ^ (divisorBoundBits b + tailBits) ∨
    (componentOrders pair unit).2 ≤
      (pair.q - 1) / 2 ^ (divisorBoundBits b + tailBits)

/-- Exact fraction of public units whose left or right CRT component has order
below the selected indexed cutoff. -/
noncomputable def generatorBadFraction {b : Nat}
    (pair : RSAKeyPairBits b) (tailBits : Nat) : Real := by
  classical
  let _ : NeZero pair.p := ⟨pair.p_prime.ne_zero⟩
  let _ : NeZero pair.q := ⟨pair.q_prime.ne_zero⟩
  let _ : NeZero pair.modulus :=
    ⟨Nat.ne_of_gt (Nat.mul_pos pair.p_prime.pos pair.q_prime.pos)⟩
  let _ : Fact pair.p.Prime := ⟨pair.p_prime⟩
  let _ : Fact pair.q.Prime := ⟨pair.q_prime⟩
  exact
    ((Finset.univ.filter fun unit : (ZMod pair.modulus)ˣ =>
        CoordinateOrderBad pair tailBits unit).card : Real) /
      Fintype.card (ZMod pair.modulus)ˣ

/-- The exact bad-unit fraction for either CRT coordinate is bounded by the
two-coordinate union bound. -/
theorem generatorBadFraction_lt {b tailBits : Nat}
    (pair : RSAKeyPairBits b) :
    generatorBadFraction pair tailBits <
      2 / ((2 ^ tailBits : Nat) : Real) := by
  classical
  let _ : NeZero pair.p := ⟨pair.p_prime.ne_zero⟩
  let _ : NeZero pair.q := ⟨pair.q_prime.ne_zero⟩
  let _ : NeZero pair.modulus :=
    ⟨Nat.ne_of_gt (Nat.mul_pos pair.p_prime.pos pair.q_prime.pos)⟩
  let _ : Fact pair.p.Prime := ⟨pair.p_prime⟩
  let _ : Fact pair.q.Prime := ⟨pair.q_prime⟩
  have htail := sampledUnit_lowOrder_tail
    (pair := pair) (tailBits := tailBits)
  have htotalPos : 0 < Fintype.card (ZMod pair.modulus)ˣ :=
    Fintype.card_pos
  have htailPos : (0 : Real) < (2 ^ tailBits : Nat) := by positivity
  have hpCard : Fintype.card (ZMod pair.p)ˣ = pair.p - 1 :=
    ZMod.card_units pair.p
  have hqCard : Fintype.card (ZMod pair.q)ˣ = pair.q - 1 :=
    ZMod.card_units pair.q
  rw [hpCard, hqCard] at htail
  unfold generatorBadFraction
  apply (div_lt_div_iff₀ (by exact_mod_cast htotalPos) htailPos).2
  norm_cast
  rw [Nat.mul_comm]
  convert htail using 1
  congr 1
  apply congrArg Finset.card
  ext unit
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- Effective specialization of the exact generator tail. -/
theorem generatorBadFraction_lt_generatorFailureBound {b : Nat}
    (pair : RSAKeyPairBits b) :
    generatorBadFraction pair (b / 64) < generatorFailureBound b := by
  simpa [generatorFailureBound] using
    generatorBadFraction_lt (pair := pair) (tailBits := b / 64)

end GeneratorOrder
end RSA
end QuantumAlg

end
