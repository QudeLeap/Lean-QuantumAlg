/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters

/-!
# The P-256 curve configuration used by the chronological window implementation

This pure configuration binds the certified public curve to the arithmetic
modulus without importing a sampling program or a proof of its action.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

open PrimeFieldShortWeierstrass

def actualCurveSpec (I : DomainParameters.PublicKeyInstance) :
    ClassicalAlgorithms.EllipticCurve.CurveSpec 256 where
  field :=
    { modulus := DomainParameters.fieldModulus
      two_le := by
        have characteristic := DomainParameters.three_lt_fieldModulus
        omega
      le_capacity := by
        have bounded := DomainParameters.primeModulus_lt_capacity
        rw [DomainParameters.fieldWidth_eq_256] at bounded
        simpa only [ClassicalAlgorithms.modulus,
          DomainParameters.fieldModulus_eq_primeModulus] using bounded.le }
  curve := DomainParameters.curve I.curveCert
  elliptic := PrimeFieldShortWeierstrass.ECDLP.Canonical.Layout.curveIsElliptic
    (DomainParameters.curve I.curveCert)

lemma actualCurveSpec_curve (I : DomainParameters.PublicKeyInstance) :
    (actualCurveSpec I).curve = DomainParameters.curve I.curveCert := rfl

lemma actualCurveSpec_modulus (I : DomainParameters.PublicKeyInstance) :
    (actualCurveSpec I).field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus := by
  change DomainParameters.fieldModulus = _
  rw [DomainParameters.fieldModulus_eq_primeModulus]
  rfl

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
