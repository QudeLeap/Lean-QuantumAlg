/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Program.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Bounds.Operand

/-!
# Short-log fixed-width fits for nearest-plane reduction

This module turns the operand-width certificate of the pure short-log
nearest-plane calculation into the numeric hypotheses consumed by its three
actual fixed-width circuits.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeNearestPlaneFits

open ClassicalAlgorithms.NumberTheory

noncomputable section

/-- All pure no-wrap conditions needed to run the three nearest-plane phases
for the reduced short-log basis and its target. -/
structure ShortLogFits (N m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) : Prop where
  fullRank : (RSA.shortLogRecoveryTrace m ell samples).output.FullRank
  third : LatticeNearestPlaneThird.Fits (RSA.ShortLogWidths.coordinateWidth N m ell)
    (RSA.shortLogRecoveryTrace m ell samples).output.first
    (RSA.shortLogRecoveryTrace m ell samples).output.second
    (RSA.shortLogRecoveryTrace m ell samples).output.third
    (RSA.shortLogLatticeTarget m ell samples)
  second : LatticeNearestPlaneSecond.Fits (RSA.ShortLogWidths.coordinateWidth N m ell)
    (RSA.shortLogRecoveryTrace m ell samples).output
    (RSA.shortLogLatticeTarget m ell samples)
  first : LatticeNearestPlaneFirst.Fits (RSA.ShortLogWidths.coordinateWidth N m ell)
    (RSA.shortLogRecoveryTrace m ell samples).output.first
    (LatticeNearestPlaneResidual.afterSecond
      (RSA.shortLogRecoveryTrace m ell samples).output
      (RSA.shortLogLatticeTarget m ell samples))
  firstDenominatorNonzero :
    LatticeNearestPlaneFirst.denominatorValue
      (RSA.shortLogRecoveryTrace m ell samples).output.first ≠ 0

/-- The short-log operand-width ledger provides every pure fixed-width
nearest-plane fit for the reduced source basis. -/
theorem shortLogFits (N m ell : Nat)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    ShortLogFits N m ell samples := by
  let basis := (RSA.shortLogRecoveryTrace m ell samples).output
  let target := RSA.shortLogLatticeTarget m ell samples
  have hfull : basis.FullRank := by
    simpa only [basis] using RSA.shortLogRecoveryTrace_fullRank m ell samples
  have hwidths : NumberTheory.NearestPlaneDivisionOperandWidthsLe basis target
      (256 * RSA.shortLogRecoveryInputBits N m ell) := by
    simpa only [basis, target] using
      RSA.shortLogNearestPlaneDivisionOperandWidthsLe N m ell samples
  have hledger : 256 * RSA.shortLogRecoveryInputBits N m ell ≤
      RSA.ShortLogWidths.operandWidthBound N m ell := by
    dsimp only [RSA.ShortLogWidths.operandWidthBound, RSA.ShortLogWidths.inputBitWidth]
    have twoPow : 2 ^ 20 = 1_048_576 := by norm_num
    rw [twoPow]
    omega
  have hthirdNumeratorWidth :
      Nat.size (LatticeNearestPlaneThird.numeratorValue
        basis.first basis.second target).natAbs ≤
        RSA.ShortLogWidths.operandWidthBound N m ell := by
    simpa only [LatticeNearestPlaneThird.numeratorValue,
      LatticeNearestPlaneThird.crossValue] using
      hwidths.thirdNumerator.trans hledger
  have hthirdDenominatorWidth :
      Nat.size (LatticeNearestPlaneThird.denominatorValue
        basis.first basis.second basis.third).natAbs ≤
        RSA.ShortLogWidths.operandWidthBound N m ell := by
    simpa only [LatticeNearestPlaneThird.denominatorValue,
      LatticeNearestPlaneThird.crossValue] using
      hwidths.thirdDenominator.trans hledger
  have hthirdDenominatorNonzero :
      LatticeNearestPlaneThird.denominatorValue
        basis.first basis.second basis.third ≠ 0 := by
    change NumberTheory.integerPointDot basis.third
      (NumberTheory.integerPointCross basis.first basis.second) ≠ 0
    rw [← basis.determinant_eq_third_dot_cross]
    exact hfull
  have hsecondNumeratorEq :
      LatticeNearestPlaneResidual.secondNumerator basis
          (LatticeNearestPlaneResidual.afterThird basis target) =
        (NumberTheory.integerPointSquaredNorm basis.first : Int) *
            NumberTheory.integerPointDot target basis.second -
          NumberTheory.integerPointDot basis.second basis.first *
            NumberTheory.integerPointDot target basis.first -
          basis.nearestPlaneThirdCoefficient target * basis.secondReductionNumerator := by
    unfold LatticeNearestPlaneResidual.secondNumerator
      LatticeNearestPlaneResidual.afterThird
      NumberTheory.IntegerBasis3.secondReductionNumerator
    simp only [NumberTheory.IntegerPoint3.sub, NumberTheory.IntegerPoint3.smul,
      NumberTheory.integerPointDot]
    ring
  have hsecondNumeratorWidth :
      Nat.size (LatticeNearestPlaneResidual.secondNumerator basis
        (LatticeNearestPlaneResidual.afterThird basis target)).natAbs ≤
        RSA.ShortLogWidths.operandWidthBound N m ell := by
    rw [hsecondNumeratorEq]
    exact hwidths.secondNumerator.trans hledger
  have hsecondDenominatorWidth :
      Nat.size basis.secondReductionDenominator.natAbs ≤
        RSA.ShortLogWidths.operandWidthBound N m ell :=
    hwidths.secondDenominator.trans hledger
  have hsecondDenominatorNonzero : basis.secondReductionDenominator ≠ 0 :=
    hfull.secondReductionDenominator_ne_zero
  have hsecondDenominatorPositive : 0 < basis.secondReductionDenominator := by
    have hnonnegative : 0 ≤ basis.secondReductionDenominator := by
      simp only [NumberTheory.IntegerBasis3.secondReductionDenominator]
      positivity
    exact lt_of_le_of_ne hnonnegative (Ne.symm hsecondDenominatorNonzero)
  have hfirstNumeratorEq :
      LatticeNearestPlaneFirst.numeratorValue
          (LatticeNearestPlaneResidual.afterSecond basis target) basis.first =
        NumberTheory.integerPointDot target basis.first -
          basis.nearestPlaneSecondCoefficient target *
            NumberTheory.integerPointDot basis.second basis.first -
          basis.nearestPlaneThirdCoefficient target *
            NumberTheory.integerPointDot basis.third basis.first := by
    unfold LatticeNearestPlaneFirst.numeratorValue
      LatticeNearestPlaneResidual.afterSecond
      LatticeNearestPlaneResidual.afterThird
    simp only [NumberTheory.IntegerPoint3.sub, NumberTheory.IntegerPoint3.smul,
      NumberTheory.integerPointDot]
    ring
  have hfirstNumeratorWidth :
      Nat.size (LatticeNearestPlaneFirst.numeratorValue
        (LatticeNearestPlaneResidual.afterSecond basis target) basis.first).natAbs ≤
        RSA.ShortLogWidths.operandWidthBound N m ell := by
    rw [hfirstNumeratorEq]
    exact hwidths.firstNumerator.trans hledger
  have hfirstDenominatorWidth :
      Nat.size (NumberTheory.integerPointSquaredNorm basis.first) ≤
        RSA.ShortLogWidths.operandWidthBound N m ell := by
    simpa only [Int.natAbs_natCast] using
      hwidths.firstDenominator.trans hledger
  have hfirstDenominatorNonzero :
      LatticeNearestPlaneFirst.denominatorValue basis.first ≠ 0 := by
    change (NumberTheory.integerPointSquaredNorm basis.first : Int) ≠ 0
    exact_mod_cast hfull.firstSquaredNorm_ne_zero
  refine ⟨hfull, ?_, ?_, ?_, hfirstDenominatorNonzero⟩
  · refine ⟨RSA.ShortLogWidths.coordinateWidth_pos N m ell, ?_, hthirdDenominatorNonzero,
      ?_, ?_⟩
    · change XGCD.signedRepresentable (RSA.ShortLogWidths.coordinateWidth N m ell)
        (if LatticeNearestPlaneThird.denominatorValue basis.first basis.second basis.third < 0
          then -LatticeNearestPlaneThird.numeratorValue basis.first basis.second target
          else LatticeNearestPlaneThird.numeratorValue basis.first basis.second target)
      apply LatticeOperandBounds.signedRepresentable_of_size_le_operandWidthBound
      by_cases hnegative : LatticeNearestPlaneThird.denominatorValue
          basis.first basis.second basis.third < 0
      · simpa only [if_pos hnegative, Int.natAbs_neg] using hthirdNumeratorWidth
      · simpa only [if_neg hnegative] using hthirdNumeratorWidth
    · exact LatticeOperandBounds.nat_lt_wordModulus_of_size_le_operandWidthBound
        hthirdDenominatorWidth
    · exact LatticeOperandBounds.signedRepresentable_of_size_le_operandWidthBound
        hthirdDenominatorWidth
  · refine ⟨RSA.ShortLogWidths.coordinateWidth_pos N m ell, ?_,
      hsecondDenominatorPositive, ?_⟩
    · exact LatticeOperandBounds.signedRepresentable_of_size_le_operandWidthBound
        hsecondNumeratorWidth
    · exact LatticeOperandBounds.nat_lt_wordModulus_of_size_le_operandWidthBound
        hsecondDenominatorWidth
  · refine ⟨RSA.ShortLogWidths.coordinateWidth_pos N m ell, ?_, ?_⟩
    · exact LatticeOperandBounds.signedRepresentable_of_size_le_operandWidthBound
        hfirstNumeratorWidth
    · exact LatticeOperandBounds.nat_lt_wordModulus_of_size_le_operandWidthBound
        hfirstDenominatorWidth

end

end LatticeNearestPlaneFits
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
