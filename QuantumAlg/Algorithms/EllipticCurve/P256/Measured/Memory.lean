/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Space
import all QuantumAlg.Util.Classical.NumberTheory.Extended.Bounds

/-!
# Proved numeric upper bounds for the complete P-256 classical allowance

The original execution coefficient widths remain the exact finite-supremum
encodings used by the actual circuit. Their polynomial upper bounds give
conservative resident and auxiliary ceilings for the same independent space
allowance. These inequalities do not assert tight peaks or replace a width,
and repetition still reuses all live storage.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

open PrimeFieldShortWeierstrass FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open ECDLP.Measured ClassicalAlgorithms.NumberTheory.XGCD

attribute [local irreducible] executionCoefficientWidth

private theorem coefficient_bits_le (coefficient : Nat → Nat)
    (sample : coefficient 261 ≤ 136506) (field : coefficient 257 ≤ 132358) (extra : Nat) :
    max (6516 + 9 * coefficient 261) (6927 + 9 * coefficient 257) + extra ≤
      1235070 + extra := by
  omega

/-- A conservative numeric upper bound on the complete original resident classical allowance. -/
theorem residentAllowance_classicalBits_le (I : DomainParameters.PublicKeyInstance) :
    let E := DomainParameters.curve I.curveCert
    let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
    SpacePool.count .classicalBits
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) +
          (PublicInput.terminal E (orderWidth problem)).residentSpace) ≤ 1237909 :=
  (residentAllowance_classicalBits I).le.trans
    (coefficient_bits_le executionCoefficientWidth
      executionCoefficientWidth_261_le executionCoefficientWidth_257_le 2839)

/-- The same auxiliary allowance omits precisely the two original borrowed public point values. -/
theorem auxiliaryAllowance_classicalBits_le (I : DomainParameters.PublicKeyInstance) :
    let E := DomainParameters.curve I.curveCert
    let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
    SpacePool.count .classicalBits
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) +
          (PublicInput.terminal E (orderWidth problem)).auxiliarySpace) ≤ 1236883 :=
  (auxiliaryAllowance_classicalBits I).le.trans
    (coefficient_bits_le executionCoefficientWidth
      executionCoefficientWidth_261_le executionCoefficientWidth_257_le 1813)

end QuantumAlg.EllipticCurve.P256.Measured
