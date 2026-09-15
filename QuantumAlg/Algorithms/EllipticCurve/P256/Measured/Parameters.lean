/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve

/-!
# Original P-256 parameters at the actual measured interface

Both the physical field word and the original nominal point coordinate have
width 256. The actual arithmetic tail parameter is therefore 255, and either
original oversampled exponent has width 260. These data proofs avoid unfolding
any executable circuit and retain the original public certificates.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

open PrimeFieldShortWeierstrass FiniteCyclicDLP

/-- The physical arithmetic word has the original 256-bit width. -/
theorem fieldModulus_size : DomainParameters.fieldModulus.size = 256 := by
  rw [DomainParameters.fieldModulus_eq_primeModulus]
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    simpa only [DomainParameters.fieldWidth_eq_256] using
      DomainParameters.primeModulus_lt_capacity
  · rw [← DomainParameters.fieldWidth_eq_256]
    exact Nat.clog_le_of_le_pow (Nat.lt_size_self DomainParameters.primeModulus).le

/-- The original nominal point coordinates have the same 256-bit field width. -/
theorem canonicalFieldWidth (cert : DomainParameters.CurveCertificate) :
    ECDLP.Canonical.Layout.fieldWidth (DomainParameters.curve cert) = 256 := by
  rw [ECDLP.Canonical.Layout.fieldWidth, DomainParameters.fieldModulus_eq_primeModulus]
  exact DomainParameters.fieldWidth_eq_256

/-- The literal actual arithmetic tail has the required original physical word size. -/
theorem fieldTail_sameWidth : Nat.succ 255 = DomainParameters.fieldModulus.size := by
  rw [fieldModulus_size]

/-- The actual arithmetic carrier strictly contains the original P-256 modulus. -/
theorem fieldTail_fits : DomainParameters.fieldModulus < 2 ^ Nat.succ 255 := by
  rw [DomainParameters.fieldModulus_eq_primeModulus]
  simpa only [DomainParameters.fieldWidth_eq_256] using
    DomainParameters.primeModulus_lt_capacity

/-- Oddness is supplied by the original prime certificate and the recorded characteristic. -/
theorem fieldModulus_odd (cert : DomainParameters.CurveCertificate) :
    Odd DomainParameters.fieldModulus :=
  cert.prime.odd_of_ne_two
    (ne_of_gt ((by norm_num : 2 < 3).trans DomainParameters.three_lt_fieldModulus))

/-- Either original known-order exponent uses the same 260 physical controls. -/
theorem orderWidth_eq_260 (I : DomainParameters.PublicKeyInstance) :
    orderWidth (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) = 260 :=
  Cascade.exponentWidth_eq_260 I

end QuantumAlg.EllipticCurve.P256.Measured
