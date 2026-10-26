/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Points

/-!
# Original public point encodings in the same window curve

Changing the presentation of the fitted coordinate width changes no point
value. The representation theorem accepts the complete original point
carrier, including infinity, and requires no prepared input or new witness.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

open PrimeFieldShortWeierstrass ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve

private def fittedCurve {p : Nat} (curve : PrimeFieldShortWeierstrass p)
    (width : Nat) (fits : p ≤ ClassicalAlgorithms.modulus width) : CurveSpec width where
  field :=
    { modulus := p
      two_le := by have bound := curve.three_lt; omega
      le_capacity := fits }
  curve := curve
  elliptic := ECDLP.Canonical.Layout.curveIsElliptic curve

private lemma pointValue_cast_width {p width : Nat} (curve : PrimeFieldShortWeierstrass p)
    (same : ECDLP.Canonical.Layout.fieldWidth curve = width)
    (fits : p ≤ ClassicalAlgorithms.modulus width) (point : curve.MathlibPoint) :
    cast (congrArg (fun n => CShape.Value (PointShape n)) same)
        (ECDLP.Canonical.Runtime.Context.pointValue curve point) =
      encodePoint (fittedCurve curve width fits) point := by
  cases same
  rfl

/-- The original fitted public-point width is exactly the arithmetic width. -/
lemma originalFieldWidth_eq_256 (I : DomainParameters.PublicKeyInstance) :
    ECDLP.Canonical.Layout.fieldWidth (DomainParameters.curve I.curveCert) = 256 := by
  simpa only [ECDLP.Canonical.Layout.fieldWidth, DomainParameters.fieldWidth,
    DomainParameters.fieldModulus_eq_primeModulus] using DomainParameters.fieldWidth_eq_256

/-- Every unchanged original point value represents the same point in the
actual window curve after the structural coordinate-width transport. -/
lemma actualCurveSpec_pointValue_represents (I : DomainParameters.PublicKeyInstance)
    (point : (DomainParameters.curve I.curveCert).MathlibPoint) :
    PointRepresents (actualCurveSpec I)
      (cast (congrArg (fun n => CShape.Value (PointShape n)) (originalFieldWidth_eq_256 I))
        (ECDLP.Canonical.Runtime.Context.pointValue (DomainParameters.curve I.curveCert) point))
      point := by
  rw [pointValue_cast_width (DomainParameters.curve I.curveCert)
    (originalFieldWidth_eq_256 I) (actualCurveSpec I).field.le_capacity]
  exact encodePoint_represents (actualCurveSpec I) point

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
