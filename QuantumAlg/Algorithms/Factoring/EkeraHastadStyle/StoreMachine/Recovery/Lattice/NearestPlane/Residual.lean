/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.LatticeReduction

/-!
# Residual-point formulas for three-dimensional nearest plane

The literal machine reduces its target in place after each coefficient.  These
pure bridges identify the second and first coefficients computed from those
residual targets with the public simultaneous nearest-plane center.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeNearestPlaneResidual

noncomputable section

/-- The determinant-quotient division used by the literal third phase is the
public third nearest-plane coefficient. -/
lemma nearestIntegerCoefficient_third
    (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) :
    NumberTheory.nearestIntegerCoefficient
        (NumberTheory.integerPointDot target
          (NumberTheory.integerPointCross basis.first basis.second))
        (NumberTheory.integerPointDot basis.third
          (NumberTheory.integerPointCross basis.first basis.second)) =
      basis.nearestPlaneThirdCoefficient target := by
  unfold NumberTheory.IntegerBasis3.nearestPlaneThirdCoefficient
    NumberTheory.IntegerBasis3.thirdOrthogonalCoordinate
    NumberTheory.nearestIntegerCoefficient
  rw [← basis.determinant_eq_third_dot_cross]

/-- Target remaining after the exact third-direction nearest-plane reduction. -/
def afterThird (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) : NumberTheory.IntegerPoint3 :=
  target.sub
    (basis.third.smul (basis.nearestPlaneThirdCoefficient target))

/-- Cleared integer numerator used for the second residual coefficient. -/
def secondNumerator (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) : Int :=
  (NumberTheory.integerPointSquaredNorm basis.first : Int) *
      NumberTheory.integerPointDot target basis.second -
    NumberTheory.integerPointDot basis.second basis.first *
      NumberTheory.integerPointDot target basis.first

/-- Computing the second coefficient from the third-reduced target agrees
with the public nearest-plane coefficient. -/
lemma nearestIntegerCoefficient_secondResidual
    (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) :
    NumberTheory.nearestIntegerCoefficient
        (secondNumerator basis (afterThird basis target))
        basis.secondReductionDenominator =
      basis.nearestPlaneSecondCoefficient target := by
  have numeratorEq : secondNumerator basis (afterThird basis target) =
      secondNumerator basis target -
        basis.nearestPlaneThirdCoefficient target * basis.secondReductionNumerator := by
    unfold secondNumerator afterThird
      NumberTheory.IntegerBasis3.secondReductionNumerator
    simp only [NumberTheory.IntegerPoint3.sub, NumberTheory.IntegerPoint3.smul,
      NumberTheory.integerPointDot]
    ring
  rw [numeratorEq]
  unfold secondNumerator
    NumberTheory.IntegerBasis3.nearestPlaneSecondCoefficient
    NumberTheory.IntegerBasis3.secondOrthogonalCoordinate
    NumberTheory.IntegerBasis3.secondGramSchmidtCoefficient
    NumberTheory.IntegerBasis3.secondReductionNumerator
    NumberTheory.IntegerBasis3.secondReductionDenominator
    NumberTheory.nearestIntegerCoefficient
  apply congrArg round
  push_cast
  ring

/-- Target remaining after the exact third- and second-direction reductions. -/
def afterSecond (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) : NumberTheory.IntegerPoint3 :=
  (afterThird basis target).sub
    (basis.second.smul (basis.nearestPlaneSecondCoefficient target))

/-- Computing the first coefficient from the twice-reduced target agrees
with the public nearest-plane coefficient. -/
lemma nearestIntegerCoefficient_firstResidual
    (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) :
    NumberTheory.nearestIntegerCoefficient
        (NumberTheory.integerPointDot (afterSecond basis target) basis.first)
        (NumberTheory.integerPointSquaredNorm basis.first) =
      basis.nearestPlaneFirstCoefficient target := by
  have numeratorEq :
      NumberTheory.integerPointDot (afterSecond basis target) basis.first =
        NumberTheory.integerPointDot target basis.first -
          basis.nearestPlaneThirdCoefficient target *
            NumberTheory.integerPointDot basis.third basis.first -
          basis.nearestPlaneSecondCoefficient target *
            NumberTheory.integerPointDot basis.second basis.first := by
    unfold afterSecond afterThird
    simp only [NumberTheory.IntegerPoint3.sub, NumberTheory.IntegerPoint3.smul,
      NumberTheory.integerPointDot]
    ring
  rw [numeratorEq]
  unfold
    NumberTheory.IntegerBasis3.nearestPlaneFirstCoefficient
    NumberTheory.IntegerBasis3.firstOrthogonalCoordinate
    NumberTheory.IntegerBasis3.firstGramSchmidtCoefficient
    NumberTheory.IntegerBasis3.thirdFirstGramSchmidtCoefficient
    NumberTheory.nearestIntegerCoefficient
  apply congrArg round
  push_cast
  ring

/-- The three sequential target reductions equal subtraction by the complete
nearest-plane lattice point. -/
lemma afterFirst_eq_sub_linearCombination
    (basis : NumberTheory.IntegerBasis3)
    (target : NumberTheory.IntegerPoint3) :
    (afterSecond basis target).sub
        (basis.first.smul (basis.nearestPlaneFirstCoefficient target)) =
      target.sub
        (basis.linearCombination (basis.nearestPlaneCoefficientCenter target)) := by
  apply Prod.ext
  · simp only [afterSecond, afterThird, NumberTheory.IntegerPoint3.sub,
      NumberTheory.IntegerPoint3.smul, NumberTheory.IntegerBasis3.linearCombination,
      NumberTheory.IntegerBasis3.nearestPlaneCoefficientCenter,
      NumberTheory.IntegerPoint3.add]
    ring
  · apply Prod.ext
    · simp only [afterSecond, afterThird, NumberTheory.IntegerPoint3.sub,
        NumberTheory.IntegerPoint3.smul, NumberTheory.IntegerBasis3.linearCombination,
        NumberTheory.IntegerBasis3.nearestPlaneCoefficientCenter,
        NumberTheory.IntegerPoint3.add]
      ring
    · simp only [afterSecond, afterThird, NumberTheory.IntegerPoint3.sub,
        NumberTheory.IntegerPoint3.smul, NumberTheory.IntegerBasis3.linearCombination,
        NumberTheory.IntegerBasis3.nearestPlaneCoefficientCenter,
        NumberTheory.IntegerPoint3.add]
      ring

end


end LatticeNearestPlaneResidual
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
