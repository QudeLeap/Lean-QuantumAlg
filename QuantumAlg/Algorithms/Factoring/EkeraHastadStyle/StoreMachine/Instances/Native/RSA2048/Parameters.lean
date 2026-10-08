/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all QuantumAlg.Util.RSA.ShortLog.Widths

/-!
# Original fixed-width data for the native RSA-2048 specialization

The resource-side key carrier retains the original ordered distinct odd
1024-bit primes and exact 2048-bit product. The stronger success-side carrier
also retains the original good-key condition.
Seven is the fixed number of complete batches, separate from the general
rational-target calibration. All widths below are mathematical scalar
facts; no circuit, runtime context or resource projection is normalized.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

noncomputable section

/-- Bit width of each prime in the fixed RSA key distribution. -/
@[expose] public def primeBits : Nat := 1_024

/-- Public bit width of a product of two fixed-distribution primes. -/
def modulusBits : Nat := 2 * primeBits

/-- The fixed number of complete shared batches in this endpoint. -/
@[expose] public def rounds : Nat := 7

/-- Exact number of fresh compiled shared arithmetic members executed by seven shared
batches of sixteen measurements each. -/
def memberExecutionCount : Nat := rounds * 16

@[simp] theorem memberExecutionCount_eq : memberExecutionCount = 112 := by
  norm_num [memberExecutionCount, rounds]

/-- The public success threshold intended for the fixed RSA-2048 endpoint. -/
def successThreshold : ENNReal := ENNReal.ofReal ((99 : Real) / 100)

/-- A theorem-side good key whose prime width is fixed to RSA-2048's
1024-bit distribution.  Its factors remain absent from the executable run. -/
@[expose] public def FixedKeyModel (N : Nat) :=
  { model : GoodKeyModel N // model.bitWidth = primeBits }

/-- Original exact-width RSA key data sufficient for resource bounds.
No good-key or common-divisor condition is required. -/
public structure FixedWidthModel (N : Nat) where
  /-- Original exact prime width, retained symbolically in the finite carrier. -/
  bitWidth : Nat
  /-- Ordered distinct odd primes with an exact double-width product. -/
  pair : RSA.RSAKeyPairBits bitWidth
  /-- The resource theorem concerns this original public modulus. -/
  modulus_eq : N = pair.modulus
  /-- The original prime width is the fixed RSA-2048 width. -/
  width_eq : bitWidth = primeBits

/-- Forget probability-side assumptions while preserving the original key and encoding. -/
public def FixedKeyModel.widthModel {N : Nat} (model : FixedKeyModel N) :
    FixedWidthModel N :=
  ⟨model.1.bitWidth, model.1.pair, model.1.modulus_eq, model.2⟩

/-- The public modulus of every fixed-width model has exactly 2048 bits. -/
theorem model_modulusBits_eq {N : Nat} (model : FixedWidthModel N) :
    Canonical.modulusBits N = modulusBits := by
  rcases model with ⟨bitWidth, pair, rfl, widthEq⟩
  change bitWidth = primeBits at widthEq
  have positive : 1 ≤ bitWidth := by
    rw [widthEq]
    norm_num [primeBits]
  simpa only [Canonical.modulusBits, ShorStyle.Canonical.modulusBits,
    modulusBits, widthEq] using
    (RSA.FixedWidthSampling.modulus_clog_eq_two_mul pair
      positive)

/-- The ordinary binary digit count of every fixed-width public modulus is
also exactly 2,048. -/
theorem model_natSize_eq {N : Nat} (model : FixedWidthModel N) :
    Nat.size N = modulusBits := by
  rcases model with ⟨bitWidth, pair, rfl, widthEq⟩
  change bitWidth = primeBits at widthEq
  have positive : 1 ≤ bitWidth := by
    rw [widthEq]
    norm_num [primeBits]
  simpa only [modulusBits, widthEq] using
    (RSA.FixedWidthSampling.modulus_size_eq_two_mul pair positive)

/-- The public arithmetic width used by the shared arithmetic carrier is also exactly 2048
bits. -/
theorem model_arithmeticBits_eq {N : Nat} (model : FixedWidthModel N) :
    Canonical.arithmeticBits N = modulusBits := by
  rcases model with ⟨bitWidth, pair, rfl, widthEq⟩
  change bitWidth = primeBits at widthEq
  change Nat.clog 2 (pair.modulus + 1) = 2 * primeBits
  apply le_antisymm
  · have capacity : pair.modulus < 2 ^ (2 * primeBits) := by
      calc
        pair.modulus < 2 ^ (2 * bitWidth) := pair.modulus_bits.2
        _ = 2 ^ (2 * primeBits) := by rw [widthEq]
    exact Nat.clog_le_of_le_pow (Nat.succ_le_of_lt capacity)
  · have strict : 2 ^ (2 * primeBits - 1) < pair.modulus + 1 := by
      calc
        2 ^ (2 * primeBits - 1) = 2 ^ (2 * bitWidth - 1) := by
          rw [widthEq]
        _ ≤ pair.modulus := pair.modulus_bits.1
        _ < pair.modulus + 1 := Nat.lt_succ_self pair.modulus
    have predecessor :
        2 * primeBits - 1 < Nat.clog 2 (pair.modulus + 1) :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).2 strict
    omega

/-- The short-log exponent register has 1,025 bits on every fixed-width
RSA-2048 model. -/
theorem model_shortLogBits_eq {N : Nat} (model : FixedWidthModel N) :
    Canonical.shortLogBits N = 1_025 := by
  unfold Canonical.shortLogBits Canonical.factorBits
  rw [model_modulusBits_eq model]
  norm_num [modulusBits, primeBits]

/-- The fixed `s = 2` tradeoff register has 513 bits on every fixed-width
RSA-2048 model. -/
theorem model_tradeoffBits_eq {N : Nat} (model : FixedWidthModel N) :
    Canonical.tradeoffBits N = 513 := by
  unfold Canonical.tradeoffBits
  rw [model_shortLogBits_eq model]

/-- One terminal short-DLP measurement contains 2,051 bits. -/
theorem model_measurementBits_eq {N : Nat} (model : FixedWidthModel N) :
    Canonical.measurementBits N = 2_051 := by
  unfold Canonical.measurementBits
  rw [model_shortLogBits_eq model, model_tradeoffBits_eq model]

/-- The uniform signed-word width of the fixed RSA-2048 lattice recovery. -/
theorem model_coordinateWidth_eq {N : Nat} (model : FixedWidthModel N) :
    RSA.ShortLogWidths.coordinateWidth N (Canonical.shortLogBits N)
      (Canonical.tradeoffBits N) = 7_522_484_226 := by
  unfold RSA.ShortLogWidths.coordinateWidth RSA.ShortLogWidths.operandWidthBound
    RSA.ShortLogWidths.inputBitWidth RSA.shortLogRecoveryInputBits
  rw [model_natSize_eq model, model_shortLogBits_eq model,
    model_tradeoffBits_eq model]
  norm_num [modulusBits, primeBits]

/-- The original explicit prime-count theorem makes the fixed key carrier nonempty. -/
theorem keygenNonempty : Nonempty (RSA.RSAKeyPairBits primeBits) := by
  apply RSA.rsaKeyPairBits_nonempty
  norm_num [primeBits]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048
