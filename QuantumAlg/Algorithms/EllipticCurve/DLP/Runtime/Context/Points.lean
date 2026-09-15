/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve
import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Model

/-!
# Original public point values

The original identity-inclusive public base and target encodings retain
their exact definitions. These are mathematical input values; no loader,
execution instruction or zero-initialization claim is introduced here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.Runtime.Context

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

open ClassicalRoutines

/-- Canonical nominal shape of one identity-inclusive curve point. -/
abbrev PointShape (E : PrimeFieldShortWeierstrass p) : CShape :=
  ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E)

/-- Canonical shaped value of one mathematical curve point. -/
def pointValue (E : PrimeFieldShortWeierstrass p) (point : E.MathlibPoint) :
    CShape.Value (PointShape E) :=
  ClassicalRoutines.EllipticCurve.encodePoint
    (Layout.curveSpec E) point

/-- Public base-point input value. -/
def baseValue (I : ECDLPInstance E) : CShape.Value (PointShape E) :=
  pointValue E I.basePoint.toMathlib

/-- Public target-point input value. -/
def targetValue (I : ECDLPInstance E) : CShape.Value (PointShape E) :=
  pointValue E I.targetPoint.toMathlib

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.Runtime.Context
