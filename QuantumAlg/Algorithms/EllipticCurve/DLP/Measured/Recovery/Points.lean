/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Group
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Points
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract

/-!
# Public point encodings and the original group target

The original public point values represent their complete mathematical curve
points, including infinity. Natural scalar multiplication in the classical
checker is exactly the multiplicative group-power target of known-order DLP.
These statements concern public values and mathematical equality; executing
their initialization remains the responsibility of the actual circuit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open ClassicalRoutines.EllipticCurve FiniteCyclicDLP

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Every public transported group point has the original complete point representation. -/
lemma publicPoint_represents (E : PrimeFieldShortWeierstrass p)
    (point : E.GroupPoint) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (Canonical.Runtime.Context.pointValue E point.toMathlib) point.toMathlib := by
  exact encodePoint_represents (Canonical.Layout.curveSpec E) point.toMathlib

/-- The original public base input represents the mathematical base point. -/
lemma publicBase_represents (problem : ECDLPInstance E) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (Canonical.Runtime.Context.baseValue problem) problem.basePoint.toMathlib := by
  exact encodePoint_represents (Canonical.Layout.curveSpec E) problem.basePoint.toMathlib

/-- The original public target input represents the mathematical target point. -/
lemma publicTarget_represents (problem : ECDLPInstance E) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (Canonical.Runtime.Context.targetValue problem) problem.targetPoint.toMathlib := by
  exact encodePoint_represents (Canonical.Layout.curveSpec E) problem.targetPoint.toMathlib

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
