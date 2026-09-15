/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Bounds.Operand
import all QuantumAlg.Util.NumberTheory.LatticeReduction.Complexity

/-!
# Fixed-width bounds for one three-dimensional LLL step

This module turns the mathematical reachable-state envelope into the exact
seven scalar range obligations consumed by the literal pair-reduction
machines.  It is independent of mutable references, routines, and traces.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeStepBounds

open ClassicalAlgorithms.NumberTheory

noncomputable section

/-- The seven scalar range obligations needed by one complete literal
three-dimensional LLL transition at a shared raw-word width. -/
structure StepFits (width : Nat) (basis : NumberTheory.IntegerBasis3) : Prop where
  widthPos : 0 < width
  firstDotRange :
    XGCD.signedRepresentable width
      (NumberTheory.integerPointDot basis.second basis.first)
  firstNormFits :
    NumberTheory.integerPointSquaredNorm basis.first < CShape.wordModulus width
  firstReducedSecondFits :
    2 * NumberTheory.integerPointSquaredNorm basis.sizeReduceFirstPair.1.second <
      CShape.wordModulus width
  secondNumeratorRange : XGCD.signedRepresentable width basis.secondReductionNumerator
  area12Fits :
    NumberTheory.integerPointAreaSquared basis.first basis.second < CShape.wordModulus width
  postSecondDotRange :
    XGCD.signedRepresentable width
      (NumberTheory.integerPointDot
        (basis.reduceThirdBySecond basis.sizeReduceSecondPair.2.1).third
        (basis.reduceThirdBySecond basis.sizeReduceSecondPair.2.1).first)
  secondReducedArea13Fits :
    2 * NumberTheory.integerPointAreaSquared basis.sizeReduceSecondPair.1.first
        basis.sizeReduceSecondPair.1.third <
      CShape.wordModulus width

/-- A natural scalar below a capacity with binary size below `width` fits in
one unsigned `width`-bit word. -/
private theorem nat_lt_wordModulus_of_le
    {width magnitude value : Nat}
    (capacity : Nat.size magnitude + 1 ≤ width)
    (valueBound : value ≤ magnitude) :
    value < CShape.wordModulus width := by
  change value < 2 ^ width
  have magnitudeFits : magnitude < 2 ^ width := by
    apply (Nat.lt_size_self magnitude).trans_le
    apply Nat.pow_le_pow_right (by decide)
    omega
  exact valueBound.trans_lt magnitudeFits

/-- An integer whose magnitude fits below the positive signed capacity of a
`width`-bit two's-complement word is signed-representable at that width. -/
private theorem signedRepresentable_of_natAbs_le
    {width magnitude : Nat} {value : Int}
    (capacity : Nat.size magnitude + 1 ≤ width)
    (valueBound : value.natAbs ≤ magnitude) :
    XGCD.signedRepresentable width value := by
  have magnitudeFits : magnitude < 2 ^ (width - 1) := by
    apply (Nat.lt_size_self magnitude).trans_le
    apply Nat.pow_le_pow_right (by decide)
    omega
  have valueFits : value.natAbs < 2 ^ (width - 1) :=
    valueBound.trans_lt magnitudeFits
  have upperNat :
      (value.natAbs : Int) < (2 ^ (width - 1) : Nat) :=
    Int.ofNat_lt.mpr valueFits
  have capacityCast :
      ((2 ^ (width - 1) : Nat) : Int) = (2 ^ (width - 1) : Int) := by
    norm_num
  unfold XGCD.signedRepresentable
  rw [← capacityCast]
  by_cases nonnegative : 0 ≤ value
  · have absEq : (value.natAbs : Int) = value :=
      Int.natAbs_of_nonneg nonnegative
    rw [absEq] at upperNat
    constructor
    · have capacityNonnegative : (0 : Int) ≤ (2 ^ (width - 1) : Nat) := by
        positivity
      omega
    · exact upperNat
  · have nonpositive : value ≤ 0 := Int.le_of_not_le nonnegative
    have absEq : (value.natAbs : Int) = -value :=
      Int.ofNat_natAbs_of_nonpos nonpositive
    rw [absEq] at upperNat
    constructor
    · omega
    · have capacityPositive : (0 : Int) < (2 ^ (width - 1) : Nat) := by
        positivity
      omega

/-- Every state in the mathematical LLL reachable-state envelope satisfies
the seven fixed-width scalar obligations once the common operand magnitude
fits below the chosen width. -/
theorem stepFits_of_boundedFrom
    {input : NumberTheory.IntegerBasis3} {state : NumberTheory.LLLState3}
    {width : Nat} (h : state.BoundedFrom input)
    (capacity :
      Nat.size (256 * (NumberTheory.lllStateEnvelope3 input + 1) ^ 8) + 1 ≤ width) :
    StepFits width state.basis := by
  let magnitude := 256 * (NumberTheory.lllStateEnvelope3 input + 1) ^ 8
  have scalarBounds := h.literalPairScalarBounds
  change
    (NumberTheory.integerPointDot state.basis.second state.basis.first).natAbs ≤ magnitude ∧
      NumberTheory.integerPointSquaredNorm state.basis.first ≤ magnitude ∧
        2 * NumberTheory.integerPointSquaredNorm
            state.basis.sizeReduceFirstPair.1.second ≤ magnitude ∧
          state.basis.secondReductionNumerator.natAbs ≤ magnitude ∧
            NumberTheory.integerPointAreaSquared state.basis.first state.basis.second ≤
              magnitude ∧
              (NumberTheory.integerPointDot
                (state.basis.reduceThirdBySecond
                  state.basis.sizeReduceSecondPair.2.1).third
                (state.basis.reduceThirdBySecond
                  state.basis.sizeReduceSecondPair.2.1).first).natAbs ≤ magnitude ∧
                2 * NumberTheory.integerPointAreaSquared
                    state.basis.sizeReduceSecondPair.1.first
                    state.basis.sizeReduceSecondPair.1.third ≤ magnitude at scalarBounds
  change Nat.size magnitude + 1 ≤ width at capacity
  rcases scalarBounds with
    ⟨firstDot, firstNorm, firstReducedSecond, secondNumerator, area12,
      postSecondDot, secondReducedArea13⟩
  refine {
    widthPos := ?_
    firstDotRange := ?_
    firstNormFits := ?_
    firstReducedSecondFits := ?_
    secondNumeratorRange := ?_
    area12Fits := ?_
    postSecondDotRange := ?_
    secondReducedArea13Fits := ?_ }
  · omega
  · exact signedRepresentable_of_natAbs_le capacity firstDot
  · exact nat_lt_wordModulus_of_le capacity firstNorm
  · exact nat_lt_wordModulus_of_le capacity firstReducedSecond
  · exact signedRepresentable_of_natAbs_le capacity secondNumerator
  · exact nat_lt_wordModulus_of_le capacity area12
  · exact signedRepresentable_of_natAbs_le capacity postSecondDot
  · exact nat_lt_wordModulus_of_le capacity secondReducedArea13

/-- The canonical short-log coordinate width exceeds the binary size of the
complete literal LLL-step scalar magnitude. -/
theorem shortLog_coordinateWidth_capacity
    (N m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    Nat.size
        (256 * (NumberTheory.lllStateEnvelope3 (RSA.shortLogLatticeBasis m ell samples) +
          1) ^ 8) +
      1 ≤ RSA.ShortLogWidths.coordinateWidth N m ell := by
  let input := RSA.shortLogLatticeBasis m ell samples
  have sourceInput : input.inputBitSize ≤ 2 * (ell + m) + 3 := by
    simpa only [input] using RSA.shortLogLatticeBasis_inputBitSize_le m ell samples
  have magnitudeSize :
      Nat.size (256 * (NumberTheory.lllStateEnvelope3 input + 1) ^ 8) ≤
        64 * (input.inputBitSize + 1) :=
    NumberTheory.lllStepOperandMagnitude_size_le input
  have linearCapacity :
      Nat.size (256 * (NumberTheory.lllStateEnvelope3 input + 1) ^ 8) + 1 ≤
        128 * (ell + m) + 257 := by
    omega
  calc
    Nat.size
        (256 * (NumberTheory.lllStateEnvelope3 (RSA.shortLogLatticeBasis m ell samples) +
          1) ^ 8) +
      1 =
        Nat.size (256 * (NumberTheory.lllStateEnvelope3 input + 1) ^ 8) + 1 := rfl
    _ ≤ 128 * (ell + m) + 257 := linearCapacity
    _ ≤ RSA.ShortLogWidths.coordinateWidth N m ell := by
      change 128 * (ell + m) + 257 ≤
        2 * (2 ^ 20 * (Nat.size N + ell + m + 1)) + 2
      have twoPow : 2 ^ 20 = 1_048_576 := by norm_num
      rw [twoPow]
      omega

/-- The initial short-log basis already satisfies the literal LLL-step
fixed-width scalar obligations at the canonical coordinate width. -/
theorem shortLog_initial_stepFits
    (N m ell : Nat) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell) :
    StepFits (RSA.ShortLogWidths.coordinateWidth N m ell)
      (RSA.shortLogLatticeBasis m ell samples) := by
  let input := RSA.shortLogLatticeBasis m ell samples
  let initial : NumberTheory.LLLState3 :=
    { basis := input, phase := .first, steps := [] }
  have fullRank : input.FullRank := by
    simpa only [input] using RSA.shortLogLatticeBasis_fullRank m ell samples
  have bounded : initial.BoundedFrom input := by
    simpa only [initial] using NumberTheory.LLLState3.boundedFrom_initial input fullRank
  have capacity := shortLog_coordinateWidth_capacity N m ell samples
  simpa only [initial, input] using stepFits_of_boundedFrom bounded capacity

end

end LatticeStepBounds
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
