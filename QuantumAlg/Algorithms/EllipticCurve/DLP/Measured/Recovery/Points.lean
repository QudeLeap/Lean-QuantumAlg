/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Group
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Points
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber

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
theorem publicPoint_represents (E : PrimeFieldShortWeierstrass p)
    (point : E.GroupPoint) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (Canonical.Runtime.Context.pointValue E point.toMathlib) point.toMathlib := by
  exact encodePoint_represents (Canonical.Layout.curveSpec E) point.toMathlib

/-- The original public base input represents the mathematical base point. -/
theorem publicBase_represents (problem : ECDLPInstance E) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (Canonical.Runtime.Context.baseValue problem) problem.basePoint.toMathlib := by
  exact encodePoint_represents (Canonical.Layout.curveSpec E) problem.basePoint.toMathlib

/-- The original public target input represents the mathematical target point. -/
theorem publicTarget_represents (problem : ECDLPInstance E) :
    PointRepresents (Canonical.Layout.curveSpec E)
      (Canonical.Runtime.Context.targetValue problem) problem.targetPoint.toMathlib := by
  exact encodePoint_represents (Canonical.Layout.curveSpec E) problem.targetPoint.toMathlib

/-- The classical point checker uses exactly the original known-order group target. -/
theorem groupScalar_eq_target_iff [Fact p.Prime]
    (problem : KnownOrderProblem E.GroupPoint) (scalar : Nat) :
    scalar • problem.generator.toMathlib = problem.target.toMathlib ↔
      problem.generator ^ scalar = problem.target := by
  rw [← Canonical.Recovery.AttemptSoundness.groupPoint_pow_toMathlib
    E problem.generator scalar]
  constructor
  · intro equality
    apply (groupPointEquiv E).injective
    exact equality
  · intro equality
    exact congrArg GroupPoint.toMathlib equality

/-- A proof-side secret witness satisfies the same classical point check. -/
theorem secret_groupScalar_eq_target [Fact p.Prime]
    (problem : KnownOrderProblem E.GroupPoint)
    (input : FiniteCyclicDLP.Canonical.Probability.SecretInput problem) :
    input.secret.val • problem.generator.toMathlib = problem.target.toMathlib := by
  exact (groupScalar_eq_target_iff problem input.secret.val).mpr input.target_eq_generator_pow

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
