/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.LatticeReduction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Bit-complexity bounds for exact three-dimensional lattice reduction

This module proves input-sensitive bounds for the explicit schoolbook charge
model emitted by the sealed reducer in `LatticeReduction`.  These are bounds
on a mathematical arithmetic schedule, not claims about Lean's bigint runtime
or wall-clock behavior.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- Binary input size used by the generic three-dimensional complexity bound. -/
def IntegerBasis3.inputBitSize (basis : IntegerBasis3) : Nat :=
  Nat.size basis.squaredHeight

/-- Uniform state envelope built from the input height, LLL potential, and
determinant magnitude. -/
def lllStateEnvelope3 (input : IntegerBasis3) : Nat :=
  let height := input.squaredHeight
  let potential := lllPotential3 input
  let determinant := input.determinant.natAbs
  height + potential + 2 * potential ^ 2 +
    potential * determinant ^ 2

/-- Natural-number form of the first Gram identity. -/
lemma firstGram_nat_identity (basis : IntegerBasis3) :
    integerPointSquaredNorm basis.first *
        integerPointSquaredNorm basis.second =
      integerPointAreaSquared basis.first basis.second +
        (integerPointDot basis.second basis.first).natAbs ^ 2 := by
  have hgram := integerPointAreaSquared_eq_gram basis.first basis.second
  rw [integerPointDot_comm basis.first basis.second] at hgram
  have hInt :
      (integerPointSquaredNorm basis.first : Int) *
          (integerPointSquaredNorm basis.second : Int) =
        (integerPointAreaSquared basis.first basis.second : Int) +
          integerPointDot basis.second basis.first ^ 2 := by
    linarith
  have hsquare :
      ((integerPointDot basis.second basis.first).natAbs : Int) ^ 2 =
        integerPointDot basis.second basis.first ^ 2 := by
    simp
  rw [← hsquare] at hInt
  exact_mod_cast hInt

/-- Natural-number three-dimensional Gram determinant decomposition. -/
lemma thirdGram_nat_identity (basis : IntegerBasis3) :
    integerPointSquaredNorm basis.first *
        integerPointAreaSquared basis.first basis.second *
          integerPointSquaredNorm basis.third =
      integerPointAreaSquared basis.first basis.second *
          (integerPointDot basis.third basis.first).natAbs ^ 2 +
        basis.secondReductionNumerator.natAbs ^ 2 +
          integerPointSquaredNorm basis.first *
            basis.determinant.natAbs ^ 2 := by
  let firstThird : IntegerBasis3 :=
    { first := basis.first, second := basis.third, third := basis.second }
  have hFirstThird := firstGram_nat_identity firstThird
  have hGramDetInt := basis.gramDeterminantIdentity
  have hnumeratorSquare :
      (basis.secondReductionNumerator.natAbs : Int) ^ 2 =
        basis.secondReductionNumerator ^ 2 := by
    simp
  have hdeterminantSquare :
      (basis.determinant.natAbs : Int) ^ 2 = basis.determinant ^ 2 := by
    simp
  rw [← hnumeratorSquare, ← hdeterminantSquare] at hGramDetInt
  have hGramDetNat :
      integerPointAreaSquared basis.first basis.second *
          integerPointAreaSquared basis.first basis.third =
        basis.secondReductionNumerator.natAbs ^ 2 +
          integerPointSquaredNorm basis.first *
            basis.determinant.natAbs ^ 2 := by
    exact_mod_cast hGramDetInt
  dsimp [firstThird] at hFirstThird
  calc
    integerPointSquaredNorm basis.first *
          integerPointAreaSquared basis.first basis.second *
            integerPointSquaredNorm basis.third =
        integerPointAreaSquared basis.first basis.second *
          (integerPointSquaredNorm basis.first *
            integerPointSquaredNorm basis.third) := by ring
    _ = integerPointAreaSquared basis.first basis.second *
          (integerPointAreaSquared basis.first basis.third +
            (integerPointDot basis.third basis.first).natAbs ^ 2) := by
      rw [hFirstThird]
    _ = integerPointAreaSquared basis.first basis.second *
          integerPointAreaSquared basis.first basis.third +
        integerPointAreaSquared basis.first basis.second *
          (integerPointDot basis.third basis.first).natAbs ^ 2 := by ring
    _ = (basis.secondReductionNumerator.natAbs ^ 2 +
          integerPointSquaredNorm basis.first *
            basis.determinant.natAbs ^ 2) +
        integerPointAreaSquared basis.first basis.second *
          (integerPointDot basis.third basis.first).natAbs ^ 2 := by
      rw [hGramDetNat]
    _ = integerPointAreaSquared basis.first basis.second *
          (integerPointDot basis.third basis.first).natAbs ^ 2 +
        basis.secondReductionNumerator.natAbs ^ 2 +
          integerPointSquaredNorm basis.first *
            basis.determinant.natAbs ^ 2 := by ring

/-- Every input row norm is bounded by the positive squared-height measure. -/
lemma IntegerBasis3.squaredNormsLe_squaredHeight (basis : IntegerBasis3) :
    basis.SquaredNormsLe basis.squaredHeight := by
  simp only [IntegerBasis3.SquaredNormsLe, IntegerBasis3.squaredHeight]
  omega

/-- The initial LLL potential is at most the cube of the positive squared
height. -/
lemma lllPotential3_le_squaredHeight_pow_three (input : IntegerBasis3) :
    lllPotential3 input ≤ input.squaredHeight ^ 3 := by
  have hnorms := input.squaredNormsLe_squaredHeight
  have harea : integerPointAreaSquared input.first input.second ≤
      integerPointSquaredNorm input.first *
        integerPointSquaredNorm input.second := by
    have hgram := firstGram_nat_identity input
    omega
  calc
    lllPotential3 input = integerPointSquaredNorm input.first *
        integerPointAreaSquared input.first input.second := rfl
    _ ≤ input.squaredHeight *
          (input.squaredHeight * input.squaredHeight) :=
      Nat.mul_le_mul hnorms.1
        (harea.trans (Nat.mul_le_mul hnorms.1 hnorms.2.1))
    _ = input.squaredHeight ^ 3 := by ring

/-- The squared determinant magnitude is at most the cube of the positive
squared height. -/
lemma IntegerBasis3.determinant_natAbs_sq_le_squaredHeight_pow_three
    (input : IntegerBasis3) :
    input.determinant.natAbs ^ 2 ≤ input.squaredHeight ^ 3 := by
  have hnorms := input.squaredNormsLe_squaredHeight
  have harea : integerPointAreaSquared input.first input.second ≤
      integerPointSquaredNorm input.first *
        integerPointSquaredNorm input.second := by
    have hgram := firstGram_nat_identity input
    omega
  have hareaHeight : integerPointAreaSquared input.first input.second ≤
      input.squaredHeight * input.squaredHeight :=
    harea.trans (Nat.mul_le_mul hnorms.1 hnorms.2.1)
  have hcauchy := integerPointDot_sq_le input.third
    (integerPointCross input.first input.second)
  rw [← input.determinant_eq_third_dot_cross] at hcauchy
  change input.determinant ^ 2 ≤
    (integerPointSquaredNorm input.third : Int) *
      (integerPointAreaSquared input.first input.second : Int) at hcauchy
  have hcast : (((input.determinant.natAbs ^ 2 : Nat) : Int)) =
      input.determinant ^ 2 := by
    simp
  rw [← hcast] at hcauchy
  have hdeterminantCauchy : input.determinant.natAbs ^ 2 ≤
      integerPointSquaredNorm input.third *
        integerPointAreaSquared input.first input.second := by
    exact_mod_cast hcauchy
  calc
    input.determinant.natAbs ^ 2 ≤ integerPointSquaredNorm input.third *
        integerPointAreaSquared input.first input.second :=
      hdeterminantCauchy
    _ ≤ input.squaredHeight *
          (input.squaredHeight * input.squaredHeight) :=
      Nat.mul_le_mul hnorms.2.2 hareaHeight
    _ = input.squaredHeight ^ 3 := by ring

/-- The input-derived reachable-state envelope is at most a fixed sixth-degree
polynomial in the positive squared height. -/
lemma lllStateEnvelope3_le_five_mul_squaredHeight_pow_six
    (input : IntegerBasis3) :
    lllStateEnvelope3 input ≤ 5 * input.squaredHeight ^ 6 := by
  let height := input.squaredHeight
  let potential := lllPotential3 input
  let determinant := input.determinant.natAbs
  have hheight : 1 ≤ height := by
    dsimp only [height, IntegerBasis3.squaredHeight]
    omega
  have hpotential : potential ≤ height ^ 3 := by
    simpa [potential, height] using
      lllPotential3_le_squaredHeight_pow_three input
  have hdeterminant : determinant ^ 2 ≤ height ^ 3 := by
    simpa [determinant, height] using
      input.determinant_natAbs_sq_le_squaredHeight_pow_three
  have hheightSix : height ≤ height ^ 6 := by
    simpa only [pow_one] using
      (pow_le_pow_right' hheight (show 1 ≤ 6 by norm_num))
  have hpotentialSix : potential ≤ height ^ 6 :=
    hpotential.trans (pow_le_pow_right' hheight (by norm_num))
  have hpotentialSquare : potential ^ 2 ≤ height ^ 6 := by
    calc
      potential ^ 2 ≤ (height ^ 3) ^ 2 :=
        Nat.pow_le_pow_left hpotential 2
      _ = height ^ 6 := by ring
  have hpotentialDeterminant :
      potential * determinant ^ 2 ≤ height ^ 6 := by
    calc
      potential * determinant ^ 2 ≤ height ^ 3 * height ^ 3 :=
        Nat.mul_le_mul hpotential hdeterminant
      _ = height ^ 6 := by ring
  change height + potential + 2 * potential ^ 2 +
      potential * determinant ^ 2 ≤ 5 * height ^ 6
  calc
    height + potential + 2 * potential ^ 2 +
          potential * determinant ^ 2 ≤
        height ^ 6 + height ^ 6 + 2 * height ^ 6 + height ^ 6 :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add hheightSix hpotentialSix)
          (Nat.mul_le_mul_left 2 hpotentialSquare))
        hpotentialDeterminant
    _ = 5 * height ^ 6 := by ring

/-- The successor of the reachable-state magnitude envelope has binary size
linear in the mathematical input bit size. -/
lemma lllStateEnvelope3_succ_size_le (input : IntegerBasis3) :
    Nat.size (lllStateEnvelope3 input + 1) ≤
      4 + 6 * input.inputBitSize := by
  let height := input.squaredHeight
  let envelope := lllStateEnvelope3 input
  have hheight : 1 ≤ height := by
    dsimp only [height, IntegerBasis3.squaredHeight]
    omega
  have hheightPow : 1 ≤ height ^ 6 := one_le_pow₀ hheight
  have henvelope : envelope ≤ 5 * height ^ 6 := by
    simpa [envelope, height] using
      lllStateEnvelope3_le_five_mul_squaredHeight_pow_six input
  have henvelopePlus : envelope + 1 ≤ 6 * height ^ 6 := by
    calc
      envelope + 1 ≤ 5 * height ^ 6 + 1 :=
        Nat.add_le_add_right henvelope 1
      _ ≤ 5 * height ^ 6 + height ^ 6 :=
        Nat.add_le_add_left hheightPow _
      _ = 6 * height ^ 6 := by ring
  have hsizeSix : Nat.size 6 = 3 := by decide
  have hsizeHeightPower : Nat.size (height ^ 6) ≤
      6 * Nat.size height + 1 :=
    natSize_pow_le_mul_add_one height 6
  calc
    Nat.size (lllStateEnvelope3 input + 1) =
        Nat.size (envelope + 1) := rfl
    _ ≤ Nat.size (6 * height ^ 6) := Nat.size_le_size henvelopePlus
    _ ≤ Nat.size 6 + Nat.size (height ^ 6) := natSize_mul_le_add _ _
    _ ≤ Nat.size 6 + (6 * Nat.size height + 1) :=
      Nat.add_le_add_left hsizeHeightPower _
    _ = 4 + 6 * input.inputBitSize := by
      rw [hsizeSix]
      simp only [IntegerBasis3.inputBitSize]
      dsimp only [height]
      ring

/-- The operand-magnitude expression used by one LLL step has binary size
linear in the mathematical input bit size. -/
lemma lllStepOperandMagnitude_size_le (input : IntegerBasis3) :
    Nat.size (256 * (lllStateEnvelope3 input + 1) ^ 8) ≤
      64 * (input.inputBitSize + 1) := by
  let height := input.squaredHeight
  let envelope := lllStateEnvelope3 input
  have hsizeEnvelope : Nat.size (envelope + 1) ≤
      4 + 6 * Nat.size height := by
    simpa [envelope, height, IntegerBasis3.inputBitSize] using
      lllStateEnvelope3_succ_size_le input
  have hsizePower : Nat.size ((envelope + 1) ^ 8) ≤
      8 * Nat.size (envelope + 1) + 1 :=
    natSize_pow_le_mul_add_one (envelope + 1) 8
  have hsize256 : Nat.size 256 = 9 := by decide
  change Nat.size (256 * (envelope + 1) ^ 8) ≤
    64 * (Nat.size height + 1)
  calc
    Nat.size (256 * (envelope + 1) ^ 8) ≤
        Nat.size 256 + Nat.size ((envelope + 1) ^ 8) :=
      natSize_mul_le_add _ _
    _ ≤ Nat.size 256 + (8 * Nat.size (envelope + 1) + 1) :=
      Nat.add_le_add_left hsizePower _
    _ ≤ Nat.size 256 + (8 * (4 + 6 * Nat.size height) + 1) :=
      Nat.add_le_add_left
        (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hsizeEnvelope) 1) _
    _ = 42 + 48 * Nat.size height := by rw [hsize256]; ring
    _ ≤ 64 * (Nat.size height + 1) := by omega

/-- The logarithmic-potential reducer budget is linear in the mathematical
input bit size. -/
lemma lllFuel3_le_eight_mul_inputBitSize (input : IntegerBasis3) :
    lllFuel3 input ≤ 8 * (input.inputBitSize + 1) := by
  let height := input.squaredHeight
  let potential := lllPotential3 input
  have hheight : 1 ≤ height := by
    dsimp only [height, IntegerBasis3.squaredHeight]
    omega
  have hheightPower : 1 ≤ height ^ 3 := one_le_pow₀ hheight
  have hpotential : potential ≤ height ^ 3 := by
    simpa [potential, height] using
      lllPotential3_le_squaredHeight_pow_three input
  have hpotentialPlus : potential + 1 ≤ 2 * height ^ 3 := by
    calc
      potential + 1 ≤ height ^ 3 + 1 :=
        Nat.add_le_add_right hpotential 1
      _ ≤ height ^ 3 + height ^ 3 :=
        Nat.add_le_add_left hheightPower _
      _ = 2 * height ^ 3 := by ring
  have hsizeTwo : Nat.size 2 = 2 := by decide
  have hsizeHeightPower : Nat.size (height ^ 3) ≤
      3 * Nat.size height + 1 :=
    natSize_pow_le_mul_add_one height 3
  have hsizePotential : Nat.size (potential + 1) ≤
      3 * Nat.size height + 3 := by
    calc
      Nat.size (potential + 1) ≤ Nat.size (2 * height ^ 3) :=
        Nat.size_le_size hpotentialPlus
      _ ≤ Nat.size 2 + Nat.size (height ^ 3) :=
        natSize_mul_le_add _ _
      _ ≤ Nat.size 2 + (3 * Nat.size height + 1) :=
        Nat.add_le_add_left hsizeHeightPower _
      _ = 3 * Nat.size height + 3 := by rw [hsizeTwo]; ring
  have hnonzero : potential + 1 ≠ 0 := by omega
  have hlogLtSize : Nat.log2 (potential + 1) <
      Nat.size (potential + 1) :=
    (Nat.log2_lt hnonzero).2 (Nat.lt_size_self _)
  have hlog : Nat.log2 (potential + 1) ≤
      3 * Nat.size height + 2 := by omega
  change 2 * (Nat.log2 (potential + 1) + 1) + 2 ≤
    8 * (Nat.size height + 1)
  omega

/-- A rational half-interval bound implies the weaker integral numerator
bound used by the state-envelope proof. -/
lemma natAbs_le_den_of_abs_div_le_half
    {numerator : Int} {denominator : Nat}
    (hdenominator : 0 < denominator)
    (hhalf :
      |(numerator : Rat) / denominator| ≤ (1 : Rat) / 2) :
    numerator.natAbs ≤ denominator := by
  have hdenominatorRat : (0 : Rat) < denominator := by
    exact_mod_cast hdenominator
  rw [abs_div, abs_of_pos hdenominatorRat] at hhalf
  have hscaled := (div_le_iff₀ hdenominatorRat).mp hhalf
  have hnumeratorRat : |(numerator : Rat)| ≤ (denominator : Rat) := by
    linarith
  have hcast : (numerator.natAbs : Rat) = |(numerator : Rat)| := by
    simp [Nat.cast_natAbs, Int.cast_abs]
  rw [← hcast] at hnumeratorRat
  exact_mod_cast hnumeratorRat

/-- First-pair size reduction bounds the new second-row norm by the global
potential and its square. -/
lemma sizeReduceFirstPair_secondNorm_le
    (basis : IntegerBasis3) (hfull : basis.FullRank) :
    integerPointSquaredNorm basis.sizeReduceFirstPair.1.second ≤
      lllPotential3 basis + lllPotential3 basis ^ 2 := by
  let reduced := basis.sizeReduceFirstPair.1
  have hfullReduced : reduced.FullRank := by
    exact hfull.sizeReduceFirstPair
  have hpotential : 0 < lllPotential3 reduced :=
    lllPotential3_pos_of_fullRank hfullReduced
  have hfirst : 0 < integerPointSquaredNorm reduced.first := by
    simpa [lllPotential3] using Nat.pos_of_mul_pos_right hpotential
  have harea :
      0 < integerPointAreaSquared reduced.first reduced.second := by
    simpa [lllPotential3] using Nat.pos_of_mul_pos_left hpotential
  have hhalf :=
    IntegerBasis3.firstGramSchmidtCoefficient_sizeReduceFirstPair basis
      hfull.firstSquaredNorm_ne_zero
  have hdot :
      (integerPointDot reduced.second reduced.first).natAbs ≤
        integerPointSquaredNorm reduced.first := by
    apply natAbs_le_den_of_abs_div_le_half hfirst
    simpa [reduced, IntegerBasis3.firstGramSchmidtCoefficient] using hhalf
  have hareaLe :
      integerPointAreaSquared reduced.first reduced.second ≤
        lllPotential3 reduced := by
    simpa [lllPotential3] using
      Nat.le_mul_of_pos_left
        (integerPointAreaSquared reduced.first reduced.second) hfirst
  have hfirstLe :
      integerPointSquaredNorm reduced.first ≤ lllPotential3 reduced := by
    simpa [lllPotential3] using
      Nat.le_mul_of_pos_right (integerPointSquaredNorm reduced.first) harea
  have hdotSq :
      (integerPointDot reduced.second reduced.first).natAbs ^ 2 ≤
        lllPotential3 reduced ^ 2 :=
    Nat.pow_le_pow_left (hdot.trans hfirstLe) 2
  calc
    integerPointSquaredNorm basis.sizeReduceFirstPair.1.second =
        integerPointSquaredNorm reduced.second := rfl
    _ ≤ integerPointSquaredNorm reduced.first *
          integerPointSquaredNorm reduced.second :=
      Nat.le_mul_of_pos_left _ hfirst
    _ = integerPointAreaSquared reduced.first reduced.second +
          (integerPointDot reduced.second reduced.first).natAbs ^ 2 :=
      firstGram_nat_identity reduced
    _ ≤ lllPotential3 reduced + lllPotential3 reduced ^ 2 :=
      Nat.add_le_add hareaLe hdotSq
    _ = lllPotential3 basis + lllPotential3 basis ^ 2 := by
      rw [lllPotential3_sizeReduceFirstPair]

/-- Second-pair size reduction bounds the new third-row norm by the potential
and determinant terms of the input basis. -/
lemma sizeReduceSecondPair_thirdNorm_le
    (basis : IntegerBasis3) (hfull : basis.FullRank) :
    integerPointSquaredNorm basis.sizeReduceSecondPair.1.third ≤
      2 * lllPotential3 basis ^ 2 +
        lllPotential3 basis * basis.determinant.natAbs ^ 2 := by
  let reduced := basis.sizeReduceSecondPair.1
  have hfullReduced : reduced.FullRank := by
    exact hfull.sizeReduceSecondPair
  have hpotential : 0 < lllPotential3 reduced :=
    lllPotential3_pos_of_fullRank hfullReduced
  have hfirst : 0 < integerPointSquaredNorm reduced.first := by
    simpa [lllPotential3] using Nat.pos_of_mul_pos_right hpotential
  have harea :
      0 < integerPointAreaSquared reduced.first reduced.second := by
    simpa [lllPotential3] using Nat.pos_of_mul_pos_left hpotential
  have hsecondHalf :=
    IntegerBasis3.secondGramSchmidtCoefficient_sizeReduceSecondPair basis
      hfull.secondReductionDenominator_ne_zero
  have hnumerator : reduced.secondReductionNumerator.natAbs ≤
      integerPointAreaSquared reduced.first reduced.second := by
    apply natAbs_le_den_of_abs_div_le_half harea
    simpa [reduced, IntegerBasis3.secondGramSchmidtCoefficient,
      IntegerBasis3.secondReductionDenominator] using hsecondHalf
  have hthirdFirstHalf :=
    IntegerBasis3.thirdFirstGramSchmidtCoefficient_sizeReduceSecondPair basis
      hfull.firstSquaredNorm_ne_zero
  have hdot :
      (integerPointDot reduced.third reduced.first).natAbs ≤
        integerPointSquaredNorm reduced.first := by
    apply natAbs_le_den_of_abs_div_le_half hfirst
    simpa [reduced, IntegerBasis3.thirdFirstGramSchmidtCoefficient] using
      hthirdFirstHalf
  have hareaLe :
      integerPointAreaSquared reduced.first reduced.second ≤
        lllPotential3 reduced := by
    simpa [lllPotential3] using
      Nat.le_mul_of_pos_left
        (integerPointAreaSquared reduced.first reduced.second) hfirst
  have hfirstLe :
      integerPointSquaredNorm reduced.first ≤ lllPotential3 reduced := by
    simpa [lllPotential3] using
      Nat.le_mul_of_pos_right (integerPointSquaredNorm reduced.first) harea
  have hdotSq :
      (integerPointDot reduced.third reduced.first).natAbs ^ 2 ≤
        integerPointSquaredNorm reduced.first ^ 2 :=
    Nat.pow_le_pow_left hdot 2
  have hnumeratorSq :
      reduced.secondReductionNumerator.natAbs ^ 2 ≤
        integerPointAreaSquared reduced.first reduced.second ^ 2 :=
    Nat.pow_le_pow_left hnumerator 2
  have hfirstTerm :
      integerPointAreaSquared reduced.first reduced.second *
          (integerPointDot reduced.third reduced.first).natAbs ^ 2 ≤
        lllPotential3 reduced ^ 2 := by
    calc
      integerPointAreaSquared reduced.first reduced.second *
            (integerPointDot reduced.third reduced.first).natAbs ^ 2 ≤
          integerPointAreaSquared reduced.first reduced.second *
            integerPointSquaredNorm reduced.first ^ 2 :=
        Nat.mul_le_mul_left _ hdotSq
      _ = lllPotential3 reduced *
            integerPointSquaredNorm reduced.first := by
        simp [lllPotential3, pow_two]
        ring
      _ ≤ lllPotential3 reduced * lllPotential3 reduced :=
        Nat.mul_le_mul_left _ hfirstLe
      _ = lllPotential3 reduced ^ 2 := by rw [pow_two]
  have hsecondTerm :
      reduced.secondReductionNumerator.natAbs ^ 2 ≤
        lllPotential3 reduced ^ 2 :=
    hnumeratorSq.trans (Nat.pow_le_pow_left hareaLe 2)
  have hdeterminant :
      reduced.determinant.natAbs = basis.determinant.natAbs := by
    simp [reduced, IntegerBasis3.sizeReduceSecondPair]
  have hthirdTerm :
      integerPointSquaredNorm reduced.first *
          reduced.determinant.natAbs ^ 2 ≤
        lllPotential3 reduced * basis.determinant.natAbs ^ 2 := by
    rw [hdeterminant]
    exact Nat.mul_le_mul_right _ hfirstLe
  calc
    integerPointSquaredNorm basis.sizeReduceSecondPair.1.third =
        integerPointSquaredNorm reduced.third := rfl
    _ ≤ integerPointSquaredNorm reduced.first *
          integerPointAreaSquared reduced.first reduced.second *
            integerPointSquaredNorm reduced.third := by
      simpa [lllPotential3, Nat.mul_assoc] using
        Nat.le_mul_of_pos_left
          (integerPointSquaredNorm reduced.third) hpotential
    _ = integerPointAreaSquared reduced.first reduced.second *
          (integerPointDot reduced.third reduced.first).natAbs ^ 2 +
        reduced.secondReductionNumerator.natAbs ^ 2 +
          integerPointSquaredNorm reduced.first *
            reduced.determinant.natAbs ^ 2 :=
      thirdGram_nat_identity reduced
    _ ≤ lllPotential3 reduced ^ 2 + lllPotential3 reduced ^ 2 +
          lllPotential3 reduced * basis.determinant.natAbs ^ 2 :=
      Nat.add_le_add (Nat.add_le_add hfirstTerm hsecondTerm) hthirdTerm
    _ = 2 * lllPotential3 reduced ^ 2 +
          lllPotential3 reduced * basis.determinant.natAbs ^ 2 := by ring
    _ = 2 * lllPotential3 basis ^ 2 +
          lllPotential3 basis * basis.determinant.natAbs ^ 2 := by
      rw [lllPotential3_sizeReduceSecondPair]

/-- Reachable-state invariant used by the generic complexity proof. -/
structure LLLState3.BoundedFrom
    (input : IntegerBasis3) (state : LLLState3) : Prop where
  /-- The current basis remains full-rank. -/
  fullRank : state.basis.FullRank
  /-- The phase-local reduction certificate remains valid. -/
  reductionInvariant : state.ReductionInvariant
  /-- The current potential is bounded by the input potential. -/
  potential_le : lllPotential3 state.basis ≤ lllPotential3 input
  /-- The determinant magnitude is invariant. -/
  determinant_eq :
    state.basis.determinant.natAbs = input.determinant.natAbs
  /-- Every current row stays within the input-derived envelope. -/
  norms_le : state.basis.SquaredNormsLe (lllStateEnvelope3 input)

/-- The initial reducer state satisfies the complete reachable-state
invariant. -/
lemma LLLState3.boundedFrom_initial
    (input : IntegerBasis3) (hfull : input.FullRank) :
    let initial : LLLState3 :=
      { basis := input, phase := .first, steps := [] }
    initial.BoundedFrom input := by
  dsimp only
  refine {
    fullRank := hfull
    reductionInvariant := ?_
    potential_le := Nat.le_refl _
    determinant_eq := rfl
    norms_le := ?_ }
  · simp [LLLState3.ReductionInvariant]
  · simp only [IntegerBasis3.SquaredNormsLe, lllStateEnvelope3,
      IntegerBasis3.squaredHeight]
    omega

/-- The first exact size-reduction result stays inside the same input-derived
row-norm envelope as every reachable state. -/
lemma LLLState3.BoundedFrom.firstSizeReduced_norms_le
    {input : IntegerBasis3} {state : LLLState3}
    (h : state.BoundedFrom input) :
    state.basis.sizeReduceFirstPair.1.SquaredNormsLe
      (lllStateEnvelope3 input) := by
  have hpotentialSq :
      lllPotential3 state.basis ^ 2 ≤ lllPotential3 input ^ 2 :=
    Nat.pow_le_pow_left h.potential_le 2
  have hsecond :
      integerPointSquaredNorm state.basis.sizeReduceFirstPair.1.second ≤
        lllStateEnvelope3 input := by
    calc
      integerPointSquaredNorm state.basis.sizeReduceFirstPair.1.second ≤
          lllPotential3 state.basis + lllPotential3 state.basis ^ 2 :=
        sizeReduceFirstPair_secondNorm_le state.basis h.fullRank
      _ ≤ lllPotential3 input + lllPotential3 input ^ 2 :=
        Nat.add_le_add h.potential_le hpotentialSq
      _ ≤ lllStateEnvelope3 input := by
        simp only [lllStateEnvelope3]
        omega
  refine ⟨?_, hsecond, ?_⟩
  · simpa [IntegerBasis3.sizeReduceFirstPair,
      IntegerBasis3.reduceSecond] using h.norms_le.1
  · simpa [IntegerBasis3.sizeReduceFirstPair,
      IntegerBasis3.reduceSecond] using h.norms_le.2.2

/-- The two-direction exact size-reduction result stays inside the same
input-derived row-norm envelope as every reachable state. -/
lemma LLLState3.BoundedFrom.secondSizeReduced_norms_le
    {input : IntegerBasis3} {state : LLLState3}
    (h : state.BoundedFrom input) :
    state.basis.sizeReduceSecondPair.1.SquaredNormsLe
      (lllStateEnvelope3 input) := by
  have hpotentialSq :
      lllPotential3 state.basis ^ 2 ≤ lllPotential3 input ^ 2 :=
    Nat.pow_le_pow_left h.potential_le 2
  have hpotentialDeterminant :
      lllPotential3 state.basis * state.basis.determinant.natAbs ^ 2 ≤
        lllPotential3 input * input.determinant.natAbs ^ 2 := by
    rw [h.determinant_eq]
    exact Nat.mul_le_mul_right _ h.potential_le
  have hthird :
      integerPointSquaredNorm state.basis.sizeReduceSecondPair.1.third ≤
        lllStateEnvelope3 input := by
    calc
      integerPointSquaredNorm state.basis.sizeReduceSecondPair.1.third ≤
          2 * lllPotential3 state.basis ^ 2 +
            lllPotential3 state.basis *
              state.basis.determinant.natAbs ^ 2 :=
        sizeReduceSecondPair_thirdNorm_le state.basis h.fullRank
      _ ≤ 2 * lllPotential3 input ^ 2 +
            lllPotential3 input * input.determinant.natAbs ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 hpotentialSq)
          hpotentialDeterminant
      _ ≤ lllStateEnvelope3 input := by
        simp only [lllStateEnvelope3]
        omega
  refine ⟨?_, ?_, hthird⟩
  · simpa [IntegerBasis3.sizeReduceSecondPair,
      IntegerBasis3.reduceThirdBySecond,
      IntegerBasis3.reduceThirdByFirst] using h.norms_le.1
  · simpa [IntegerBasis3.sizeReduceSecondPair,
      IntegerBasis3.reduceThirdBySecond,
      IntegerBasis3.reduceThirdByFirst] using h.norms_le.2.1

/-- Every scalar consumed by the two literal pair reductions is bounded by
the common reachable-state arithmetic magnitude. -/
lemma LLLState3.BoundedFrom.literalPairScalarBounds
    {input : IntegerBasis3} {state : LLLState3}
    (h : state.BoundedFrom input) :
    let magnitude := 256 * (lllStateEnvelope3 input + 1) ^ 8
    (integerPointDot state.basis.second state.basis.first).natAbs ≤ magnitude ∧
      integerPointSquaredNorm state.basis.first ≤ magnitude ∧
        2 * integerPointSquaredNorm
            state.basis.sizeReduceFirstPair.1.second ≤ magnitude ∧
          state.basis.secondReductionNumerator.natAbs ≤ magnitude ∧
            integerPointAreaSquared state.basis.first state.basis.second ≤ magnitude ∧
              (integerPointDot
                (state.basis.reduceThirdBySecond
                  state.basis.sizeReduceSecondPair.2.1).third
                (state.basis.reduceThirdBySecond
                  state.basis.sizeReduceSecondPair.2.1).first).natAbs ≤
                  magnitude ∧
                2 * integerPointAreaSquared state.basis.sizeReduceSecondPair.1.first
                    state.basis.sizeReduceSecondPair.1.third ≤ magnitude := by
  exact lllPairScalarBounds_of_reduced state.basis
    (lllStateEnvelope3 input) h.fullRank h.norms_le
    h.firstSizeReduced_norms_le h.secondSizeReduced_norms_le

/-- The actual arithmetic emitted by one reachable reducer state has a uniform
input-derived operand-width bound. -/
lemma LLLState3.BoundedFrom.step_maxOperandWidth_le
    {input : IntegerBasis3} {state : LLLState3}
    (h : state.BoundedFrom input) :
    arithmeticEventListMaxOperandWidth
        (lllStepExecution3 state).arithmetic ≤
      Nat.size (256 * (lllStateEnvelope3 input + 1) ^ 8) :=
  lllStepExecution3_maxOperandWidth_le_of_reduced state
    (lllStateEnvelope3 input) h.fullRank h.norms_le
    h.firstSizeReduced_norms_le h.secondSizeReduced_norms_le

/-- One reducer step preserves the complete input-derived state envelope. -/
lemma LLLState3.BoundedFrom.step
    {input : IntegerBasis3} {state : LLLState3}
    (h : state.BoundedFrom input) :
    (lllStep3 state).BoundedFrom input := by
  refine {
    fullRank := lllStep3_fullRank state h.fullRank
    reductionInvariant :=
      lllStep3_reductionInvariant state h.fullRank h.reductionInvariant
    potential_le := (lllStep3_potential_le state h.fullRank).trans h.potential_le
    determinant_eq := (lllStep3_determinant_natAbs state).trans h.determinant_eq
    norms_le := lllStep3_squaredNormsLe_of_reduced state
      (lllStateEnvelope3 input) h.norms_le
        h.firstSizeReduced_norms_le h.secondSizeReduced_norms_le }

/-- Every fixed-fuel reducer run preserves the complete input-derived state
envelope. -/
lemma lllRun3_boundedFrom (fuel : Nat)
    {input : IntegerBasis3} {state : LLLState3}
    (h : state.BoundedFrom input) :
    (lllRun3 fuel state).BoundedFrom input := by
  induction fuel generalizing state with
  | zero => simpa [lllRun3] using h
  | succ fuel ih =>
      rw [lllRun3]
      exact ih h.step

/-- The public fixed-fuel reducer exposes the same input-derived row-norm
envelope preserved by its internal state machine. -/
lemma lllReduce3WithFuel_output_squaredNormsLe
    (fuel : Nat) (basis : IntegerBasis3) (hfull : basis.FullRank) :
    (lllReduce3WithFuel fuel basis).output.SquaredNormsLe
      (lllStateEnvelope3 basis) := by
  rw [lllReduce3WithFuel_output_eq_finalBasis]
  let initial : LLLState3 :=
    { basis := basis, phase := .first, steps := [] }
  have hinitial : initial.BoundedFrom basis := by
    simpa [initial] using LLLState3.boundedFrom_initial basis hfull
  exact (lllRun3_boundedFrom fuel hinitial).norms_le

/-- Every arithmetic operand in a reachable fixed-fuel execution has width
linear in the original basis input size. -/
lemma lllRunExecution3_maxOperandWidth_le (fuel : Nat)
    {input : IntegerBasis3} {state : LLLState3}
    (h : state.BoundedFrom input) :
    arithmeticEventListMaxOperandWidth
        (lllRunExecution3 fuel state).arithmetic ≤
      64 * (input.inputBitSize + 1) := by
  induction fuel generalizing state with
  | zero => simp [lllRunExecution3, arithmeticEventListMaxOperandWidth]
  | succ fuel ih =>
      simp only [lllRunExecution3,
        arithmeticEventListMaxOperandWidth_append]
      apply max_le
      · exact h.step_maxOperandWidth_le.trans
          (lllStepOperandMagnitude_size_le input)
      · apply ih
        change (lllStep3 state).BoundedFrom input
        exact h.step

/-- A fixed-fuel execution has an explicit quadratic-per-bit schoolbook charge
bound, multiplied only by its actual iteration budget. -/
lemma lllRunExecution3_schoolbookCharge_le (fuel : Nat)
    {input : IntegerBasis3} {state : LLLState3}
    (h : state.BoundedFrom input) :
    arithmeticEventListCharge
        (lllRunExecution3 fuel state).arithmetic ≤
      1_537_900 * fuel * (input.inputBitSize + 1) ^ 2 := by
  let events := (lllRunExecution3 fuel state).arithmetic
  have hlength : events.length ≤ 91 * fuel := by
    simpa [events] using lllRunExecution3_arithmetic_length_le fuel state
  have hwidth : arithmeticEventListMaxOperandWidth events ≤
      64 * (input.inputBitSize + 1) := by
    simpa [events] using lllRunExecution3_maxOperandWidth_le fuel h
  have hwidthSucc : arithmeticEventListMaxOperandWidth events + 1 ≤
      65 * (input.inputBitSize + 1) := by
    calc
      arithmeticEventListMaxOperandWidth events + 1 ≤
          64 * (input.inputBitSize + 1) + 1 :=
        Nat.add_le_add_right hwidth 1
      _ ≤ 65 * (input.inputBitSize + 1) := by omega
  have hwidthSquare :
      (arithmeticEventListMaxOperandWidth events + 1) ^ 2 ≤
        (65 * (input.inputBitSize + 1)) ^ 2 :=
    Nat.pow_le_pow_left hwidthSucc 2
  calc
    arithmeticEventListCharge
          (lllRunExecution3 fuel state).arithmetic =
        arithmeticEventListCharge events := rfl
    _ ≤ 4 * events.length *
          (arithmeticEventListMaxOperandWidth events + 1) ^ 2 :=
      arithmeticEventListCharge_le events
    _ ≤ 4 * (91 * fuel) *
          (65 * (input.inputBitSize + 1)) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4 hlength) hwidthSquare
    _ = 1_537_900 * fuel * (input.inputBitSize + 1) ^ 2 := by ring

/-- The public fixed-fuel reducer exposes exactly the schoolbook charge bounded
by the sealed execution theorem above. -/
lemma lllReduce3WithFuel_schoolbookCharge_le
    (fuel : Nat) (basis : IntegerBasis3) (hfull : basis.FullRank) :
    (lllReduce3WithFuel fuel basis).schoolbookCharge ≤
      1_537_900 * fuel * (basis.inputBitSize + 1) ^ 2 := by
  let initial : LLLState3 :=
    { basis := basis, phase := .first, steps := [] }
  have hinitial : initial.BoundedFrom basis := by
    simpa [initial] using LLLState3.boundedFrom_initial basis hfull
  change arithmeticEventListCharge
      (lllRunExecution3 fuel initial).arithmetic ≤ _
  exact lllRunExecution3_schoolbookCharge_le fuel hinitial

/-- The complete exact three-dimensional reducer has an explicit cubic
schoolbook-charge bound in its growing binary input size. -/
lemma lllReduce3_schoolbookCharge_le
    (basis : IntegerBasis3) (hfull : basis.FullRank) :
    (lllReduce3 basis).schoolbookCharge ≤
      12_303_200 * (basis.inputBitSize + 1) ^ 3 := by
  let initial : LLLState3 :=
    { basis := basis, phase := .first, steps := [] }
  have hinitial : initial.BoundedFrom basis := by
    simpa [initial] using LLLState3.boundedFrom_initial basis hfull
  have hcharge : arithmeticEventListCharge
      (lllRunExecution3 (lllFuel3 basis) initial).arithmetic ≤
        1_537_900 * lllFuel3 basis *
          (basis.inputBitSize + 1) ^ 2 :=
    lllRunExecution3_schoolbookCharge_le (lllFuel3 basis) hinitial
  have hfuel := lllFuel3_le_eight_mul_inputBitSize basis
  change arithmeticEventListCharge
      (lllRunExecution3 (lllFuel3 basis) initial).arithmetic ≤ _
  calc
    arithmeticEventListCharge
          (lllRunExecution3 (lllFuel3 basis) initial).arithmetic ≤
        1_537_900 * lllFuel3 basis *
          (basis.inputBitSize + 1) ^ 2 := hcharge
    _ ≤ 1_537_900 * (8 * (basis.inputBitSize + 1)) *
          (basis.inputBitSize + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1_537_900 hfuel)
    _ = 12_303_200 * (basis.inputBitSize + 1) ^ 3 := by ring

end NumberTheory
end QuantumAlg

end
