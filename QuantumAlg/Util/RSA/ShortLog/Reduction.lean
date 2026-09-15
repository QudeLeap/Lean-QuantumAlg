/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.CenteredResidue
import all QuantumAlg.Util.NumberTheory.ExactArithmetic
import all QuantumAlg.Util.NumberTheory.LatticeReduction.Complexity
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quantum-free Ekerå–Håstad RSA reduction

The public modulus and an internally sampled unit determine a short discrete
logarithm.  Recovering that logarithm determines the two RSA factors through a
quadratic equation.  This module contains only deterministic arithmetic; key
generation and probability bounds live in sibling modules.
-/

section

namespace QuantumAlg
namespace RSA

/-- Hidden short logarithm used by the Ekerå–Håstad RSA reduction. -/
def shortLogSecret (p q : Nat) : Nat :=
  (p + q - 2) / 2

/-- Public exponent used to form the short-DLP target `g^((N-1)/2)`. -/
def targetExponent (N : Nat) : Nat :=
  (N - 1) / 2

/-- The public target exponent never needs more bits than the modulus. -/
private theorem targetExponent_size_le (N : Nat) :
    Nat.size (targetExponent N) ≤ Nat.size N := by
  apply Nat.size_le_size
  unfold targetExponent
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

/-- Target group element computed from the public modulus and sampled unit. -/
def targetUnit {N : Nat} (generator : (ZMod N)ˣ) : (ZMod N)ˣ :=
  generator ^ targetExponent N

/-- One decoded pair from the two exponent registers of the short-logarithm
circuit. -/
abbrev ShortLogSample (m ell : Nat) : Type :=
  Fin (2 ^ (ell + m)) × Fin (2 ^ ell)

/-- Three integer coefficients for the source lattice basis: the shared
short-log coordinate followed by the two period coordinates. -/
abbrev ShortLogLatticeCoefficients : Type :=
  NumberTheory.IntegerPoint3

/-- One concrete point in the three-dimensional `s = 2` source lattice. -/
abbrev ShortLogLatticePoint : Type :=
  NumberTheory.IntegerPoint3

/-- Modulus used by the two measured exponent-register coordinates. -/
def shortLogLatticeModulus (m ell : Nat) : Nat :=
  2 ^ (ell + m)

/-- Public binary-size envelope for one complete two-sample short-logarithm
recovery. -/
def shortLogRecoveryInputBits (N m ell : Nat) : Nat :=
  Nat.size N + ell + m + 1

/-- Ordered row basis of the actual three-dimensional `s = 2` source
lattice [EH17, source.tex:675-696]. -/
def shortLogLatticeBasis (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    NumberTheory.IntegerBasis3 where
  first := (samples.1.1.val, samples.2.1.val, 1)
  second := (shortLogLatticeModulus m ell, 0, 0)
  third := (0, shortLogLatticeModulus m ell, 0)

/-- Determinant of the source basis is the square of its positive register
modulus. -/
theorem shortLogLatticeBasis_determinant (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogLatticeBasis m ell samples).determinant =
      (shortLogLatticeModulus m ell : Int) ^ 2 := by
  simp [shortLogLatticeBasis, NumberTheory.IntegerBasis3.determinant,
    NumberTheory.integerPointCross, NumberTheory.integerPointDot]
  ring

/-- The explicit source basis has full rank for every register width. -/
theorem shortLogLatticeBasis_fullRank (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogLatticeBasis m ell samples).FullRank := by
  unfold NumberTheory.IntegerBasis3.FullRank
  rw [shortLogLatticeBasis_determinant]
  exact pow_ne_zero 2 (by
    exact_mod_cast (show shortLogLatticeModulus m ell ≠ 0 by
      simp [shortLogLatticeModulus]))

/-- The concrete two-sample source basis has squared height bounded by four
times the square of the public register modulus. -/
theorem shortLogLatticeBasis_squaredHeight_le (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogLatticeBasis m ell samples).squaredHeight ≤
      4 * shortLogLatticeModulus m ell ^ 2 := by
  let modulus := shortLogLatticeModulus m ell
  have hfirstLt : samples.1.1.val < modulus := by
    change samples.1.1.val < 2 ^ (ell + m)
    exact samples.1.1.isLt
  have hsecondLt : samples.2.1.val < modulus := by
    change samples.2.1.val < 2 ^ (ell + m)
    exact samples.2.1.isLt
  have hfirstSq : samples.1.1.val ^ 2 < modulus ^ 2 :=
    Nat.pow_lt_pow_left hfirstLt (by norm_num)
  have hsecondSq : samples.2.1.val ^ 2 < modulus ^ 2 :=
    Nat.pow_lt_pow_left hsecondLt (by norm_num)
  have hraw :
      1 + (samples.1.1.val ^ 2 + samples.2.1.val ^ 2 + 1) +
          modulus ^ 2 + modulus ^ 2 ≤ 4 * modulus ^ 2 := by
    omega
  simpa [NumberTheory.IntegerBasis3.squaredHeight,
    shortLogLatticeBasis, NumberTheory.integerPointSquaredNorm, modulus]
    using hraw

/-- Binary input size of the concrete short-log source basis is linear in the
two public register widths. -/
theorem shortLogLatticeBasis_inputBitSize_le (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogLatticeBasis m ell samples).inputBitSize ≤
      2 * (ell + m) + 3 := by
  have hheight := shortLogLatticeBasis_squaredHeight_le m ell samples
  have hpower :
      4 * shortLogLatticeModulus m ell ^ 2 =
        2 ^ (2 * (ell + m) + 2) := by
    simp only [shortLogLatticeModulus]
    calc
      4 * (2 ^ (ell + m)) ^ 2 =
          2 ^ 2 * 2 ^ ((ell + m) * 2) := by
        rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_mul]
      _ = 2 ^ (2 + (ell + m) * 2) := by rw [pow_add]
      _ = 2 ^ (2 * (ell + m) + 2) := by
        congr 1
        omega
  calc
    (shortLogLatticeBasis m ell samples).inputBitSize =
        Nat.size (shortLogLatticeBasis m ell samples).squaredHeight := rfl
    _ ≤ Nat.size (4 * shortLogLatticeModulus m ell ^ 2) :=
      Nat.size_le_size hheight
    _ = Nat.size (2 ^ (2 * (ell + m) + 2)) := by rw [hpower]
    _ = 2 * (ell + m) + 3 := by
      rw [Nat.size_pow]

/-- Exact LLL potential of the source basis.  Writing it out makes the public
iteration bound independent of an asymptotic LLL iteration estimate. -/
theorem shortLogLatticeBasis_potential (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    NumberTheory.lllPotential3 (shortLogLatticeBasis m ell samples) =
      (samples.1.1.val ^ 2 + samples.2.1.val ^ 2 + 1) *
        ((shortLogLatticeModulus m ell) ^ 2 +
          (samples.2.1.val * shortLogLatticeModulus m ell) ^ 2) := by
  simp [NumberTheory.lllPotential3, shortLogLatticeBasis,
    NumberTheory.integerPointSquaredNorm,
    NumberTheory.integerPointAreaSquared,
    NumberTheory.integerPointCross, Int.natAbs_mul]

/-- The source-basis potential is bounded by a power whose exponent is linear
in the two public register widths. -/
theorem shortLogLatticeBasis_potential_succ_lt_pow (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    NumberTheory.lllPotential3 (shortLogLatticeBasis m ell samples) + 1 <
      2 ^ (6 * (ell + m) + 4) := by
  let modulus := shortLogLatticeModulus m ell
  have hmodulusPos : 0 < modulus := by
    simp [modulus, shortLogLatticeModulus]
  have hfirstLt : samples.1.1.val < modulus := by
    change samples.1.1.val < 2 ^ (ell + m)
    exact samples.1.1.isLt
  have hsecondLt : samples.2.1.val < modulus := by
    change samples.2.1.val < 2 ^ (ell + m)
    exact samples.2.1.isLt
  have hfirstSq : samples.1.1.val ^ 2 < modulus ^ 2 :=
    Nat.pow_lt_pow_left hfirstLt (by norm_num)
  have hsecondSq : samples.2.1.val ^ 2 < modulus ^ 2 :=
    Nat.pow_lt_pow_left hsecondLt (by norm_num)
  have hnormLt :
      samples.1.1.val ^ 2 + samples.2.1.val ^ 2 + 1 <
        2 * modulus ^ 2 := by
    omega
  have hfactorLe : samples.2.1.val ^ 2 + 1 ≤ modulus ^ 2 := by
    omega
  have hareaEq :
      modulus ^ 2 + (samples.2.1.val * modulus) ^ 2 =
        (samples.2.1.val ^ 2 + 1) * modulus ^ 2 := by
    ring
  have hareaLe :
      modulus ^ 2 + (samples.2.1.val * modulus) ^ 2 ≤ modulus ^ 4 := by
    rw [hareaEq]
    calc
      (samples.2.1.val ^ 2 + 1) * modulus ^ 2 ≤
          modulus ^ 2 * modulus ^ 2 :=
        Nat.mul_le_mul_right (modulus ^ 2) hfactorLe
      _ = modulus ^ 4 := by ring
  have hareaPos :
      0 < modulus ^ 2 + (samples.2.1.val * modulus) ^ 2 := by
    positivity
  have hproductLt :
      (samples.1.1.val ^ 2 + samples.2.1.val ^ 2 + 1) *
          (modulus ^ 2 + (samples.2.1.val * modulus) ^ 2) <
        2 * modulus ^ 6 := by
    calc
      _ < (2 * modulus ^ 2) *
          (modulus ^ 2 + (samples.2.1.val * modulus) ^ 2) :=
        Nat.mul_lt_mul_of_pos_right hnormLt hareaPos
      _ ≤ (2 * modulus ^ 2) * modulus ^ 4 :=
        Nat.mul_le_mul_left _ hareaLe
      _ = 2 * modulus ^ 6 := by ring
  have hpotentialLe :
      NumberTheory.lllPotential3 (shortLogLatticeBasis m ell samples) + 1 ≤
        2 * modulus ^ 6 := by
    rw [shortLogLatticeBasis_potential]
    simpa [modulus] using (Nat.succ_le_iff.mpr hproductLt)
  calc
    NumberTheory.lllPotential3 (shortLogLatticeBasis m ell samples) + 1 ≤
        2 * modulus ^ 6 := hpotentialLe
    _ < 16 * modulus ^ 6 :=
      Nat.mul_lt_mul_of_pos_right (by norm_num) (pow_pos hmodulusPos 6)
    _ = 2 ^ (6 * (ell + m) + 4) := by
      change 16 * (2 ^ (ell + m)) ^ 6 = 2 ^ (6 * (ell + m) + 4)
      rw [show 16 = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega

/-- Public padded LLL iteration budget for every two-sample basis of the given
register widths.  It is linear in those widths and independent of the measured
values. -/
def shortLogRecoveryFuel (m ell : Nat) : Nat :=
  12 * (ell + m) + 10

/-- The public padded fuel remains linear in the register widths. -/
theorem shortLogRecoveryFuel_le (m ell : Nat) :
    shortLogRecoveryFuel m ell ≤ 12 * (ell + m + 1) := by
  simp only [shortLogRecoveryFuel]
  omega

/-- The linear public fuel dominates the exact logarithmic state measure of
every source basis. -/
theorem shortLogLatticeBasis_initialMeasure_lt_fuel (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    NumberTheory.lllStateMeasure3
        { basis := shortLogLatticeBasis m ell samples
          phase := .first
          steps := [] } <
      shortLogRecoveryFuel m ell := by
  have hpotential :=
    shortLogLatticeBasis_potential_succ_lt_pow m ell samples
  have hlog :
      Nat.log2
          (NumberTheory.lllPotential3
            (shortLogLatticeBasis m ell samples) + 1) <
        6 * (ell + m) + 4 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.succ_ne_zero _) hpotential
  have hmono :
      Nat.log2
          (NumberTheory.lllPotential3
            (shortLogLatticeBasis m ell samples)) ≤
        Nat.log2
          (NumberTheory.lllPotential3
            (shortLogLatticeBasis m ell samples) + 1) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.le_add_right _ _)
  simp only [NumberTheory.lllStateMeasure3,
    NumberTheory.lllPhasePenalty3, shortLogRecoveryFuel]
  omega

/-- Auditable exact LLL trace used by the short-logarithm recovery. -/
def shortLogRecoveryTrace (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    NumberTheory.LatticeReductionTrace3 :=
  NumberTheory.lllReduce3WithFuel (shortLogRecoveryFuel m ell)
    (shortLogLatticeBasis m ell samples)

/-- The short-logarithm recovery trace spans the source lattice. -/
theorem shortLogRecoveryTrace_spans (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogLatticeBasis m ell samples).SameLattice
      (shortLogRecoveryTrace m ell samples).output :=
  NumberTheory.lllReduce3WithFuel_spans _ _

/-- The trace output is a complete exact `δ = 1/2` LLL-reduced basis. -/
theorem shortLogRecoveryTrace_isReduced (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogRecoveryTrace m ell samples).output.IsReduced :=
  NumberTheory.lllReduce3WithFuel_isReduced _ _
    (shortLogLatticeBasis_fullRank m ell samples)
    (shortLogLatticeBasis_initialMeasure_lt_fuel m ell samples)

/-- The reduced short-logarithm basis remains full rank. -/
theorem shortLogRecoveryTrace_fullRank (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogRecoveryTrace m ell samples).output.FullRank :=
  NumberTheory.lllReduce3WithFuel_fullRank _ _
    (shortLogLatticeBasis_fullRank m ell samples)

/-- Every actual short-log reduction records the same exact number of padded
replay slots. -/
theorem shortLogRecoveryTrace_steps_length (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogRecoveryTrace m ell samples).steps.length =
      3 * shortLogRecoveryFuel m ell :=
  NumberTheory.lllReduce3WithFuel_steps_length _ _

/-- Exact-arithmetic schoolbook charge of the LLL subtrace is cubic in the
public short-log register width.  Candidate enumeration and validation are
separate executable stages and are not included in this bound. -/
theorem shortLogRecoveryTrace_schoolbookCharge_le (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogRecoveryTrace m ell samples).schoolbookCharge ≤
      295_276_800 * (ell + m + 1) ^ 3 := by
  let basis := shortLogLatticeBasis m ell samples
  have hfull : basis.FullRank := by
    simpa [basis] using shortLogLatticeBasis_fullRank m ell samples
  have hcharge :
      (shortLogRecoveryTrace m ell samples).schoolbookCharge ≤
        1_537_900 * shortLogRecoveryFuel m ell *
          (basis.inputBitSize + 1) ^ 2 := by
    simpa [shortLogRecoveryTrace, basis] using
      NumberTheory.lllReduce3WithFuel_schoolbookCharge_le
        (shortLogRecoveryFuel m ell) basis hfull
  have hfuel :
      shortLogRecoveryFuel m ell ≤ 12 * (ell + m + 1) :=
    shortLogRecoveryFuel_le m ell
  have hinputBits : basis.inputBitSize ≤ 2 * (ell + m) + 3 := by
    simpa [basis] using shortLogLatticeBasis_inputBitSize_le m ell samples
  have hbits : basis.inputBitSize + 1 ≤ 4 * (ell + m + 1) := by
    omega
  have hbitsSq :
      (basis.inputBitSize + 1) ^ 2 ≤
        (4 * (ell + m + 1)) ^ 2 :=
    Nat.pow_le_pow_left hbits 2
  calc
    (shortLogRecoveryTrace m ell samples).schoolbookCharge ≤
        1_537_900 * shortLogRecoveryFuel m ell *
          (basis.inputBitSize + 1) ^ 2 := hcharge
    _ ≤ 1_537_900 * (12 * (ell + m + 1)) *
          (4 * (ell + m + 1)) ^ 2 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left 1_537_900 hfuel)
        hbitsSq
    _ = 295_276_800 * (ell + m + 1) ^ 3 := by ring

/-- Every operand in the sealed padded reduction fits a linear envelope in
the complete public short-log input width. -/
private theorem shortLogRecoveryTrace_maxOperandWidth_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogRecoveryTrace m ell samples).maxOperandWidth ≤
      256 * shortLogRecoveryInputBits N m ell := by
  let basis := shortLogLatticeBasis m ell samples
  let inputBits := shortLogRecoveryInputBits N m ell
  let initial : NumberTheory.LLLState3 :=
    { basis := basis, phase := .first, steps := [] }
  have hfull : basis.FullRank := by
    simpa [basis] using shortLogLatticeBasis_fullRank m ell samples
  have hinitial : initial.BoundedFrom basis := by
    simpa [initial] using
      NumberTheory.LLLState3.boundedFrom_initial basis hfull
  have htraceArithmetic :
      (shortLogRecoveryTrace m ell samples).arithmetic =
        (NumberTheory.lllRunExecution3 (shortLogRecoveryFuel m ell)
          initial).arithmetic := by
    rfl
  have hraw :
      (shortLogRecoveryTrace m ell samples).maxOperandWidth ≤
        64 * (basis.inputBitSize + 1) := by
    change NumberTheory.arithmeticEventListMaxOperandWidth
        (shortLogRecoveryTrace m ell samples).arithmetic ≤ _
    rw [htraceArithmetic]
    exact
      NumberTheory.lllRunExecution3_maxOperandWidth_le
        (shortLogRecoveryFuel m ell) hinitial
  have hsourceInput : basis.inputBitSize ≤ 2 * (ell + m) + 3 := by
    simpa [basis] using shortLogLatticeBasis_inputBitSize_le m ell samples
  have hbits : 64 * (basis.inputBitSize + 1) ≤ 256 * inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  exact hraw.trans hbits

/-- Source lattice row-span map for two measured pairs.

The rows are `(j₁,j₂,1)`, `(2^(ell+m),0,0)`, and
`(0,2^(ell+m),0)` [EH17, source.tex:675-696]. -/
def shortLogLatticePoint (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (coefficients : ShortLogLatticeCoefficients) : ShortLogLatticePoint :=
  let shared := coefficients.1
  let firstPeriod := coefficients.2.1
  let secondPeriod := coefficients.2.2
  let modulus : Int := shortLogLatticeModulus m ell
  (shared * samples.1.1.val + firstPeriod * modulus,
    shared * samples.2.1.val + secondPeriod * modulus,
    shared)

/-- The source row-span map is exactly linear combination in the explicit
integer basis. -/
theorem shortLogLatticeBasis_linearCombination (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (coefficients : ShortLogLatticeCoefficients) :
    (shortLogLatticeBasis m ell samples).linearCombination coefficients =
      shortLogLatticePoint m ell samples coefficients := by
  apply Prod.ext
  · simp [shortLogLatticeBasis, shortLogLatticePoint,
      NumberTheory.IntegerBasis3.linearCombination,
      NumberTheory.IntegerPoint3.add, NumberTheory.IntegerPoint3.smul]
  · apply Prod.ext
    · simp [shortLogLatticeBasis, shortLogLatticePoint,
        NumberTheory.IntegerBasis3.linearCombination,
        NumberTheory.IntegerPoint3.add, NumberTheory.IntegerPoint3.smul]
    · simp [shortLogLatticeBasis, shortLogLatticePoint,
        NumberTheory.IntegerBasis3.linearCombination,
        NumberTheory.IntegerPoint3.add, NumberTheory.IntegerPoint3.smul]

/-- Coordinate-vector view of one concrete source lattice point. -/
def shortLogLatticeVector (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (coefficients : ShortLogLatticeCoefficients) :
    NumberTheory.IntegerVector 3 :=
  (shortLogLatticePoint m ell samples coefficients).toVector

/-- Centered target vector used by the source neighborhood search. -/
def shortLogTargetCoordinate (m ell : Nat)
    (sample : ShortLogSample m ell) : Int :=
  let modulus := shortLogLatticeModulus m ell
  NumberTheory.centeredResidue modulus
    (NumberTheory.modularNegation modulus (2 ^ m * sample.2.val))

/-- Centered source error attached to one measured pair and a proposed short
logarithm. -/
def shortLogErrorCoordinate (m ell secret : Nat)
    (sample : ShortLogSample m ell) : Int :=
  NumberTheory.centeredResidue (shortLogLatticeModulus m ell)
    (secret * sample.1.val + 2 ^ m * sample.2.val)

/-- Centered target vector used by the source neighborhood search. -/
def shortLogLatticeTarget (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    ShortLogLatticePoint :=
  (shortLogTargetCoordinate m ell samples.1,
    shortLogTargetCoordinate m ell samples.2,
    0)

/-- The centered two-coordinate target has squared norm bounded by twice the
square of the public register modulus. -/
theorem shortLogLatticeTarget_squaredNorm_le (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    NumberTheory.integerPointSquaredNorm
        (shortLogLatticeTarget m ell samples) ≤
      2 * shortLogLatticeModulus m ell ^ 2 := by
  have hmodulus : 0 < shortLogLatticeModulus m ell := by
    simp [shortLogLatticeModulus]
  have hfirstTwice :
      2 * (shortLogTargetCoordinate m ell samples.1).natAbs ≤
        shortLogLatticeModulus m ell := by
    simpa [shortLogTargetCoordinate] using
      (NumberTheory.two_mul_natAbs_centeredResidue_le
        (value := NumberTheory.modularNegation
          (shortLogLatticeModulus m ell) (2 ^ m * samples.1.2.val))
        hmodulus)
  have hsecondTwice :
      2 * (shortLogTargetCoordinate m ell samples.2).natAbs ≤
        shortLogLatticeModulus m ell := by
    simpa [shortLogTargetCoordinate] using
      (NumberTheory.two_mul_natAbs_centeredResidue_le
        (value := NumberTheory.modularNegation
          (shortLogLatticeModulus m ell) (2 ^ m * samples.2.2.val))
        hmodulus)
  have hfirst : (shortLogTargetCoordinate m ell samples.1).natAbs ≤
      shortLogLatticeModulus m ell := by omega
  have hsecond : (shortLogTargetCoordinate m ell samples.2).natAbs ≤
      shortLogLatticeModulus m ell := by omega
  have hfirstSq := Nat.pow_le_pow_left hfirst 2
  have hsecondSq := Nat.pow_le_pow_left hsecond 2
  simp only [shortLogLatticeTarget,
    NumberTheory.integerPointSquaredNorm, Int.natAbs_zero]
  omega

/-- Input-derived squared-norm envelope for every row of the reduced source
basis. -/
private def shortLogReducedBasisBound (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) : Nat :=
  NumberTheory.lllStateEnvelope3 (shortLogLatticeBasis m ell samples)

/-- Input-derived magnitude envelope used by the exact nearest-plane trace. -/
private def shortLogNearestPlaneOperandMagnitude (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) : Nat :=
  let modulus := shortLogLatticeModulus m ell
  let basisBound := shortLogReducedBasisBound m ell samples
  4096 * (2 * modulus ^ 2 + 1) * (basisBound + 1) ^ 8

/-- The nearest-plane magnitude envelope has linear binary size in the public
short-log input envelope. -/
private theorem shortLogNearestPlaneOperandMagnitude_size_succ_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    Nat.size (shortLogNearestPlaneOperandMagnitude m ell samples) + 1 ≤
      256 * shortLogRecoveryInputBits N m ell := by
  let source := shortLogLatticeBasis m ell samples
  let modulus := shortLogLatticeModulus m ell
  let basisBound := shortLogReducedBasisBound m ell samples
  let targetBound := 2 * modulus ^ 2
  let inputBits := shortLogRecoveryInputBits N m ell
  let operandMagnitude := shortLogNearestPlaneOperandMagnitude m ell samples
  have hsourceInput : source.inputBitSize ≤ 2 * (ell + m) + 3 := by
    simpa [source] using shortLogLatticeBasis_inputBitSize_le m ell samples
  have hbasisSize : Nat.size (basisBound + 1) ≤
      12 * (ell + m) + 22 := by
    calc
      Nat.size (basisBound + 1) ≤ 4 + 6 * source.inputBitSize := by
        simpa [basisBound, shortLogReducedBasisBound, source] using
          NumberTheory.lllStateEnvelope3_succ_size_le source
      _ ≤ 4 + 6 * (2 * (ell + m) + 3) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 6 hsourceInput) 4
      _ = 12 * (ell + m) + 22 := by ring
  have hmodulusPos : 0 < modulus := by
    simp [modulus, shortLogLatticeModulus]
  have hmodulusSqPos : 1 ≤ modulus ^ 2 := one_le_pow₀ hmodulusPos
  have htargetSucc : targetBound + 1 ≤ 3 * modulus ^ 2 := by
    dsimp only [targetBound]
    omega
  have htargetSize : Nat.size (targetBound + 1) ≤
      2 * (ell + m + 1) + 3 := by
    have hsizeThree : Nat.size 3 = 2 := by decide
    calc
      Nat.size (targetBound + 1) ≤ Nat.size (3 * modulus ^ 2) :=
        Nat.size_le_size htargetSucc
      _ ≤ Nat.size 3 + Nat.size (modulus ^ 2) :=
        NumberTheory.natSize_mul_le_add _ _
      _ ≤ Nat.size 3 + (2 * Nat.size modulus + 1) :=
        Nat.add_le_add_left
          (NumberTheory.natSize_pow_le_mul_add_one modulus 2) _
      _ = 2 * (ell + m + 1) + 3 := by
        rw [hsizeThree]
        simp [modulus, shortLogLatticeModulus, Nat.size_pow]
        ring
  have hpowerSize : Nat.size ((basisBound + 1) ^ 8) ≤
      8 * Nat.size (basisBound + 1) + 1 :=
    NumberTheory.natSize_pow_le_mul_add_one _ _
  have hsize4096 : Nat.size 4096 = 13 := by decide
  have hmagnitudeSize : Nat.size operandMagnitude ≤
      98 * (ell + m) + 195 := by
    calc
      Nat.size operandMagnitude =
          Nat.size ((4096 * (targetBound + 1)) *
            (basisBound + 1) ^ 8) := by
        simp only [operandMagnitude, shortLogNearestPlaneOperandMagnitude,
          targetBound, basisBound, modulus]
      _ ≤ Nat.size (4096 * (targetBound + 1)) +
          Nat.size ((basisBound + 1) ^ 8) :=
        NumberTheory.natSize_mul_le_add _ _
      _ ≤ (Nat.size 4096 + Nat.size (targetBound + 1)) +
          Nat.size ((basisBound + 1) ^ 8) :=
        Nat.add_le_add_right
          (NumberTheory.natSize_mul_le_add 4096 (targetBound + 1)) _
      _ ≤ (Nat.size 4096 + (2 * (ell + m + 1) + 3)) +
          (8 * Nat.size (basisBound + 1) + 1) :=
        Nat.add_le_add (Nat.add_le_add_left htargetSize _) hpowerSize
      _ ≤ (Nat.size 4096 + (2 * (ell + m + 1) + 3)) +
          (8 * (12 * (ell + m) + 22) + 1) :=
        Nat.add_le_add_left
          (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hbasisSize) 1) _
      _ = 98 * (ell + m) + 195 := by
        rw [hsize4096]
        ring
  calc
    Nat.size (shortLogNearestPlaneOperandMagnitude m ell samples) + 1 =
        Nat.size operandMagnitude + 1 := rfl
    _ ≤ 98 * (ell + m) + 196 := Nat.add_le_add_right hmagnitudeSize 1
    _ ≤ 256 * inputBits := by
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega

/-- The exact nearest-plane stage of short-log recovery has cubic schoolbook
charge in the public binary input envelope. -/
theorem shortLogNearestPlaneTrace_schoolbookCharge_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (NumberTheory.nearestPlaneTrace3
      (shortLogRecoveryTrace m ell samples).output
      (shortLogLatticeTarget m ell samples)).schoolbookCharge ≤
        2 ^ 31 * shortLogRecoveryInputBits N m ell ^ 3 := by
  let source := shortLogLatticeBasis m ell samples
  let reduced := (shortLogRecoveryTrace m ell samples).output
  let modulus := shortLogLatticeModulus m ell
  let basisBound := shortLogReducedBasisBound m ell samples
  let targetBound := 2 * modulus ^ 2
  let inputBits := shortLogRecoveryInputBits N m ell
  let operandMagnitude := shortLogNearestPlaneOperandMagnitude m ell samples
  have hoperandBits : Nat.size operandMagnitude + 1 ≤ 256 * inputBits := by
    simpa [operandMagnitude, inputBits] using
      shortLogNearestPlaneOperandMagnitude_size_succ_le N m ell samples
  have hfull : reduced.FullRank := by
    simpa [reduced] using shortLogRecoveryTrace_fullRank m ell samples
  have hbasis : reduced.SquaredNormsLe basisBound := by
    simpa [reduced, basisBound, shortLogReducedBasisBound, source,
      shortLogRecoveryTrace] using
      (NumberTheory.lllReduce3WithFuel_output_squaredNormsLe
        (shortLogRecoveryFuel m ell) source
        (shortLogLatticeBasis_fullRank m ell samples))
  have htarget : NumberTheory.integerPointSquaredNorm
      (shortLogLatticeTarget m ell samples) ≤ targetBound := by
    simpa [targetBound, modulus] using
      shortLogLatticeTarget_squaredNorm_le m ell samples
  have hraw := NumberTheory.nearestPlaneTrace3_schoolbookCharge_le
    reduced (shortLogLatticeTarget m ell samples) basisBound targetBound
      hfull hbasis htarget
  have hinputBitsPos : 1 ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  calc
    (NumberTheory.nearestPlaneTrace3 reduced
        (shortLogLatticeTarget m ell samples)).schoolbookCharge ≤
        276 * (Nat.size operandMagnitude + 1) ^ 2 := by
      simpa [operandMagnitude, shortLogNearestPlaneOperandMagnitude,
        targetBound, basisBound, shortLogReducedBasisBound, modulus,
        source] using hraw
    _ ≤ 276 * (256 * inputBits) ^ 2 :=
      Nat.mul_le_mul_left 276 (Nat.pow_le_pow_left hoperandBits 2)
    _ = 18_087_936 * inputBits ^ 2 := by ring
    _ ≤ 2 ^ 31 * inputBits ^ 3 :=
      Nat.mul_le_mul (by norm_num)
        (pow_le_pow_right' hinputBitsPos (by norm_num))
    _ = 2 ^ 31 * shortLogRecoveryInputBits N m ell ^ 3 := rfl

/-- Every operand in the sealed nearest-plane stage fits the same linear
short-log input envelope used by its candidate consumers. -/
theorem shortLogNearestPlaneTrace_maxOperandWidth_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (NumberTheory.nearestPlaneTrace3
      (shortLogRecoveryTrace m ell samples).output
      (shortLogLatticeTarget m ell samples)).maxOperandWidth ≤
        256 * shortLogRecoveryInputBits N m ell := by
  let source := shortLogLatticeBasis m ell samples
  let reduced := (shortLogRecoveryTrace m ell samples).output
  let modulus := shortLogLatticeModulus m ell
  let basisBound := shortLogReducedBasisBound m ell samples
  let targetBound := 2 * modulus ^ 2
  let inputBits := shortLogRecoveryInputBits N m ell
  let operandMagnitude := shortLogNearestPlaneOperandMagnitude m ell samples
  have hoperandBits : Nat.size operandMagnitude + 1 ≤ 256 * inputBits := by
    simpa [operandMagnitude, inputBits] using
      shortLogNearestPlaneOperandMagnitude_size_succ_le N m ell samples
  have hfull : reduced.FullRank := by
    simpa [reduced] using shortLogRecoveryTrace_fullRank m ell samples
  have hbasis : reduced.SquaredNormsLe basisBound := by
    simpa [reduced, basisBound, shortLogReducedBasisBound, source,
      shortLogRecoveryTrace] using
      (NumberTheory.lllReduce3WithFuel_output_squaredNormsLe
        (shortLogRecoveryFuel m ell) source
        (shortLogLatticeBasis_fullRank m ell samples))
  have htarget : NumberTheory.integerPointSquaredNorm
      (shortLogLatticeTarget m ell samples) ≤ targetBound := by
    simpa [targetBound, modulus] using
      shortLogLatticeTarget_squaredNorm_le m ell samples
  have hraw := NumberTheory.nearestPlaneTrace3_maxOperandWidth_le
    reduced (shortLogLatticeTarget m ell samples) basisBound targetBound
      hfull hbasis htarget
  have hwidth :
      (NumberTheory.nearestPlaneTrace3 reduced
        (shortLogLatticeTarget m ell samples)).maxOperandWidth ≤
        256 * inputBits := by
    calc
      (NumberTheory.nearestPlaneTrace3 reduced
          (shortLogLatticeTarget m ell samples)).maxOperandWidth ≤
          Nat.size operandMagnitude := by
        simpa [operandMagnitude, shortLogNearestPlaneOperandMagnitude,
          targetBound, basisBound, shortLogReducedBasisBound, modulus,
          source] using hraw
      _ ≤ Nat.size operandMagnitude + 1 := Nat.le_succ _
      _ ≤ 256 * inputBits := hoperandBits
  simpa [reduced, inputBits] using hwidth

/-- The six rounded-division operands used by the short-log nearest-plane
stage fit the public linear input-width envelope. -/
theorem shortLogNearestPlaneDivisionOperandWidthsLe
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    NumberTheory.NearestPlaneDivisionOperandWidthsLe
      (shortLogRecoveryTrace m ell samples).output
      (shortLogLatticeTarget m ell samples)
      (256 * shortLogRecoveryInputBits N m ell) := by
  let source := shortLogLatticeBasis m ell samples
  let reduced := (shortLogRecoveryTrace m ell samples).output
  let modulus := shortLogLatticeModulus m ell
  let basisBound := shortLogReducedBasisBound m ell samples
  let targetBound := 2 * modulus ^ 2
  let inputBits := shortLogRecoveryInputBits N m ell
  let operandMagnitude := shortLogNearestPlaneOperandMagnitude m ell samples
  have hoperandBits : Nat.size operandMagnitude + 1 ≤ 256 * inputBits := by
    simpa [operandMagnitude, inputBits] using
      shortLogNearestPlaneOperandMagnitude_size_succ_le N m ell samples
  have hfull : reduced.FullRank := by
    simpa [reduced] using shortLogRecoveryTrace_fullRank m ell samples
  have hbasis : reduced.SquaredNormsLe basisBound := by
    simpa [reduced, basisBound, shortLogReducedBasisBound, source,
      shortLogRecoveryTrace] using
      (NumberTheory.lllReduce3WithFuel_output_squaredNormsLe
        (shortLogRecoveryFuel m ell) source
        (shortLogLatticeBasis_fullRank m ell samples))
  have htarget : NumberTheory.integerPointSquaredNorm
      (shortLogLatticeTarget m ell samples) ≤ targetBound := by
    simpa [targetBound, modulus] using
      shortLogLatticeTarget_squaredNorm_le m ell samples
  have hoperands : NumberTheory.NearestPlaneDivisionOperandsLe reduced
      (shortLogLatticeTarget m ell samples) operandMagnitude := by
    simpa [operandMagnitude, shortLogNearestPlaneOperandMagnitude,
      NumberTheory.nearestPlaneArithmeticEnvelope3, targetBound, basisBound,
      shortLogReducedBasisBound, modulus, source] using
      (NumberTheory.nearestPlaneDivisionOperandsLe_of_bounds
        reduced (shortLogLatticeTarget m ell samples) basisBound targetBound
        hfull hbasis htarget)
  have hwidth : NumberTheory.NearestPlaneDivisionOperandWidthsLe reduced
      (shortLogLatticeTarget m ell samples) (256 * inputBits) := by
    exact hoperands.toWidths ((Nat.le_succ _).trans hoperandBits)
  simpa [reduced, inputBits] using hwidth

/-- Membership in the actual row span of the source lattice. -/
def ShortLogLatticeMember (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (point : ShortLogLatticePoint) : Prop :=
  ∃ coefficients, shortLogLatticePoint m ell samples coefficients = point

/-- Coordinatewise difference of two concrete three-dimensional lattice
points. -/
def shortLogLatticePointSub (left right : ShortLogLatticePoint) :
    ShortLogLatticePoint :=
  (left.1 - right.1, left.2.1 - right.2.1, left.2.2 - right.2.2)

/-- The row-span lattice is closed under coordinatewise subtraction. -/
theorem ShortLogLatticeMember.sub
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    {left right : ShortLogLatticePoint}
    (hleft : ShortLogLatticeMember m ell samples left)
    (hright : ShortLogLatticeMember m ell samples right) :
    ShortLogLatticeMember m ell samples
      (shortLogLatticePointSub left right) := by
  rcases hleft with ⟨leftCoefficients, rfl⟩
  rcases hright with ⟨rightCoefficients, rfl⟩
  refine ⟨(leftCoefficients.1 - rightCoefficients.1,
    leftCoefficients.2.1 - rightCoefficients.2.1,
    leftCoefficients.2.2 - rightCoefficients.2.2), ?_⟩
  apply Prod.ext
  · simp [shortLogLatticePoint, shortLogLatticePointSub]
    ring
  · apply Prod.ext
    · simp [shortLogLatticePoint, shortLogLatticePointSub]
      ring
    · simp [shortLogLatticePoint, shortLogLatticePointSub]

/-- Absence of the precise short-vector obstruction from Ekerå–Håstad's
Lemma 4 specialized to `s = 2`: every lattice vector whose three coordinates
are strictly smaller than `2^(m-3)` is zero
[EH17, source.tex:737-776]. -/
def ShortLogNoTinyVector (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) : Prop :=
  ∀ point, ShortLogLatticeMember m ell samples point →
    point.1.natAbs < 2 ^ (m - 3) →
    point.2.1.natAbs < 2 ^ (m - 3) →
    point.2.2.natAbs < 2 ^ (m - 3) →
    point = (0, 0, 0)

/-- On the source no-tiny-vector event, the first vector of the reduced basis
has squared norm at least the square of the source threshold. -/
theorem shortLogRecoveryTrace_firstSquaredNorm_lower
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hnoTiny : ShortLogNoTinyVector m ell samples) :
    (2 ^ (m - 3)) ^ 2 ≤
      NumberTheory.integerPointSquaredNorm
        (shortLogRecoveryTrace m ell samples).output.first := by
  let basis := (shortLogRecoveryTrace m ell samples).output
  let threshold := 2 ^ (m - 3)
  have hfull : basis.FullRank := by
    simpa [basis] using shortLogRecoveryTrace_fullRank m ell samples
  have hfirstNe : basis.first ≠ (0, 0, 0) := by
    intro hzero
    apply hfull.firstSquaredNorm_ne_zero
    exact (NumberTheory.integerPointSquaredNorm_eq_zero_iff basis.first).mpr
      hzero
  have houtputMember :
      ∃ coefficients, basis.linearCombination coefficients = basis.first := by
    refine ⟨(1, 0, 0), ?_⟩
    simp [NumberTheory.IntegerBasis3.linearCombination,
      NumberTheory.IntegerPoint3.smul, NumberTheory.IntegerPoint3.add]
  have hsourceMemberRaw :
      ∃ coefficients,
        (shortLogLatticeBasis m ell samples).linearCombination coefficients =
          basis.first := by
    exact (shortLogRecoveryTrace_spans m ell samples basis.first).mpr
      houtputMember
  have hsourceMember :
      ShortLogLatticeMember m ell samples basis.first := by
    rcases hsourceMemberRaw with ⟨coefficients, hcoefficients⟩
    rw [shortLogLatticeBasis_linearCombination] at hcoefficients
    exact ⟨coefficients, hcoefficients⟩
  by_contra hnot
  have hnormLt : NumberTheory.integerPointSquaredNorm basis.first <
      threshold ^ 2 := Nat.lt_of_not_ge (by simpa [basis, threshold] using hnot)
  have hfirstSq : basis.first.1.natAbs ^ 2 < threshold ^ 2 := by
    have hle : basis.first.1.natAbs ^ 2 ≤
        NumberTheory.integerPointSquaredNorm basis.first := by
      simp only [NumberTheory.integerPointSquaredNorm]
      omega
    exact hle.trans_lt hnormLt
  have hsecondSq : basis.first.2.1.natAbs ^ 2 < threshold ^ 2 := by
    have hle : basis.first.2.1.natAbs ^ 2 ≤
        NumberTheory.integerPointSquaredNorm basis.first := by
      simp only [NumberTheory.integerPointSquaredNorm]
      omega
    exact hle.trans_lt hnormLt
  have hthirdSq : basis.first.2.2.natAbs ^ 2 < threshold ^ 2 := by
    have hle : basis.first.2.2.natAbs ^ 2 ≤
        NumberTheory.integerPointSquaredNorm basis.first := by
      simp only [NumberTheory.integerPointSquaredNorm]
      omega
    exact hle.trans_lt hnormLt
  have hthresholdPos : 0 < threshold := by
    simp [threshold]
  have hfirstTiny : basis.first.1.natAbs < threshold := by
    nlinarith
  have hsecondTiny : basis.first.2.1.natAbs < threshold := by
    nlinarith
  have hthirdTiny : basis.first.2.2.natAbs < threshold := by
    nlinarith
  exact hfirstNe <| hnoTiny basis.first hsourceMember
    (by simpa [threshold] using hfirstTiny)
    (by simpa [threshold] using hsecondTiny)
    (by simpa [threshold] using hthirdTiny)

/-! ### Finite count of first-register short-vector obstructions -/

/-- First-register obstruction to the no-tiny-vector condition.  A positive
shared multiplier shorter than `2^(m-3)` makes both first-register products
land in the same centered window. -/
def ShortLogTinyMultiplierObstruction (m ell : Nat)
    (indices : Fin (2 ^ (ell + m)) × Fin (2 ^ (ell + m))) : Prop :=
  ∃ multiplier : Nat,
    0 < multiplier ∧ multiplier < 2 ^ (m - 3) ∧
      NumberTheory.centeredModDistance (2 ^ (ell + m))
          (multiplier * indices.1.val) < 2 ^ (m - 3) ∧
      NumberTheory.centeredModDistance (2 ^ (ell + m))
          (multiplier * indices.2.val) < 2 ^ (m - 3)

/-- First-register indices made tiny by one fixed positive multiplier. -/
def shortLogTinyFirstIndexSet (m ell multiplier : Nat) :
    Finset (Fin (2 ^ (ell + m))) := by
  classical
  exact Finset.univ.filter fun index =>
    NumberTheory.centeredModDistance (2 ^ (ell + m))
        (multiplier * index.val) < 2 ^ (m - 3)

/-- Ordered first-register pairs obstructed by one fixed multiplier. -/
def shortLogTinyPairSetForMultiplier (m ell multiplier : Nat) :
    Finset (Fin (2 ^ (ell + m)) × Fin (2 ^ (ell + m))) :=
  shortLogTinyFirstIndexSet m ell multiplier ×ˢ
    shortLogTinyFirstIndexSet m ell multiplier

/-- Complete finite union of ordered first-register obstruction pairs. -/
def shortLogTinyMultiplierObstructionPairs (m ell : Nat) :
    Finset (Fin (2 ^ (ell + m)) × Fin (2 ^ (ell + m))) := by
  classical
  exact (Finset.Ico 1 (2 ^ (m - 3))).biUnion fun multiplier =>
    shortLogTinyPairSetForMultiplier m ell multiplier

/-- Membership in the finite obstruction carrier is exactly the existence of
a short positive shared multiplier. -/
theorem mem_shortLogTinyMultiplierObstructionPairs_iff
    {m ell : Nat}
    {indices : Fin (2 ^ (ell + m)) × Fin (2 ^ (ell + m))} :
    indices ∈ shortLogTinyMultiplierObstructionPairs m ell ↔
      ShortLogTinyMultiplierObstruction m ell indices := by
  classical
  constructor
  · intro hindices
    rw [shortLogTinyMultiplierObstructionPairs,
      Finset.mem_biUnion] at hindices
    rcases hindices with ⟨multiplier, hmultiplier, hpair⟩
    rw [Finset.mem_Ico] at hmultiplier
    unfold shortLogTinyPairSetForMultiplier at hpair
    have hpair' := Finset.mem_product.mp hpair
    have hfirst := (Finset.mem_filter.mp hpair'.1).2
    have hsecond := (Finset.mem_filter.mp hpair'.2).2
    exact ⟨multiplier, hmultiplier.1, hmultiplier.2,
      hfirst, hsecond⟩
  · rintro ⟨multiplier, hpositive, hshort, hfirst, hsecond⟩
    rw [shortLogTinyMultiplierObstructionPairs,
      Finset.mem_biUnion]
    refine ⟨multiplier, ?_, ?_⟩
    · exact Finset.mem_Ico.mpr ⟨hpositive, hshort⟩
    · unfold shortLogTinyPairSetForMultiplier
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsecond⟩

/-- The exact 2-adic window count bounds the bad first-register indices for
one short positive multiplier. -/
theorem card_shortLogTinyFirstIndexSet_le
    {m ell multiplier : Nat} (hm : 3 ≤ m)
    (hmultiplierPos : 0 < multiplier)
    (hmultiplierLt : multiplier < 2 ^ (m - 3)) :
    (shortLogTinyFirstIndexSet m ell multiplier).card ≤ 2 ^ (m - 2) := by
  have hwindow : m - 3 ≤ ell + m := by omega
  simpa [shortLogTinyFirstIndexSet, show m - 3 + 1 = m - 2 by omega] using
    (NumberTheory.card_centered_mul_pow_two_window_lt_le hwindow
      hmultiplierPos hmultiplierLt)

/-- One fixed multiplier obstructs at most the square of its one-coordinate
window count. -/
theorem card_shortLogTinyPairSetForMultiplier_le
    {m ell multiplier : Nat} (hm : 3 ≤ m)
    (hmultiplierPos : 0 < multiplier)
    (hmultiplierLt : multiplier < 2 ^ (m - 3)) :
    (shortLogTinyPairSetForMultiplier m ell multiplier).card ≤
      (2 ^ (m - 2)) ^ 2 := by
  unfold shortLogTinyPairSetForMultiplier
  rw [Finset.card_product]
  simpa [pow_two] using Nat.mul_le_mul
    (card_shortLogTinyFirstIndexSet_le (m := m) (ell := ell)
      (multiplier := multiplier) hm hmultiplierPos hmultiplierLt)
    (card_shortLogTinyFirstIndexSet_le (m := m) (ell := ell)
      (multiplier := multiplier) hm hmultiplierPos hmultiplierLt)

/-- Union bound for every tiny first-register pair.  This counts the actual
uniform first-register carrier and makes no conditional-uniformity assumption
about narrow-good outcomes [EH17, source.tex:737-776]. -/
theorem card_shortLogTinyMultiplierObstructionPairs_le
    {m ell : Nat} (hm : 3 ≤ m) :
    (shortLogTinyMultiplierObstructionPairs m ell).card ≤
      2 ^ (m - 3) * (2 ^ (m - 2)) ^ 2 := by
  classical
  calc
    (shortLogTinyMultiplierObstructionPairs m ell).card ≤
        ∑ multiplier ∈ Finset.Ico 1 (2 ^ (m - 3)),
          (shortLogTinyPairSetForMultiplier m ell multiplier).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _multiplier ∈ Finset.Ico 1 (2 ^ (m - 3)),
          (2 ^ (m - 2)) ^ 2 := by
      apply Finset.sum_le_sum
      intro multiplier hmultiplier
      have hrange := Finset.mem_Ico.mp hmultiplier
      exact card_shortLogTinyPairSetForMultiplier_le hm
        hrange.1 hrange.2
    _ = (2 ^ (m - 3) - 1) * (2 ^ (m - 2)) ^ 2 := by
      simp [Finset.sum_const]
    _ ≤ 2 ^ (m - 3) * (2 ^ (m - 2)) ^ 2 := by
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- Whenever the tradeoff register rounds upward enough that `m ≤ 2*ell`,
the finite obstruction set is at most one 128th of the complete ordered
first-register pair space.  In particular this covers the canonical
`ell = ceil(m/2)` choice for `s = 2`. -/
theorem card_shortLogTinyMultiplierObstructionPairs_mul_128_le_square
    {m ell : Nat} (hm : 3 ≤ m) (htradeoff : m ≤ 2 * ell) :
    (shortLogTinyMultiplierObstructionPairs m ell).card * 128 ≤
      (2 ^ (ell + m)) ^ 2 := by
  have hcard := card_shortLogTinyMultiplierObstructionPairs_le (m := m)
    (ell := ell) hm
  calc
    (shortLogTinyMultiplierObstructionPairs m ell).card * 128 ≤
        (2 ^ (m - 3) * (2 ^ (m - 2)) ^ 2) * 128 :=
      Nat.mul_le_mul_right 128 hcard
    _ = 2 ^ (3 * m) := by
      rw [show 128 = 2 ^ 7 by norm_num, pow_two,
        ← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (2 * (ell + m)) := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    _ = (2 ^ (ell + m)) ^ 2 := by
      rw [show 2 * (ell + m) = (ell + m) * 2 by omega, pow_mul]

/-- Excluding the finite short-multiplier obstruction forces the precise
no-tiny-vector condition used by the fixed-dimensional lattice search. -/
theorem shortLogNoTinyVector_of_noTinyMultiplierObstruction
    {m ell : Nat} (samples : ShortLogSample m ell × ShortLogSample m ell)
    (hm : 3 ≤ m)
    (hclear : ¬ ShortLogTinyMultiplierObstruction m ell
      (samples.1.1, samples.2.1)) :
    ShortLogNoTinyVector m ell samples := by
  intro point hmember hfirst hsecond hthird
  rcases hmember with ⟨coefficients, rfl⟩
  let shared := coefficients.1
  let firstPeriod := coefficients.2.1
  let secondPeriod := coefficients.2.2
  let modulus : Int := shortLogLatticeModulus m ell
  let threshold : Nat := 2 ^ (m - 3)
  have hthresholdLtModulus : threshold < shortLogLatticeModulus m ell := by
    dsimp [threshold]
    unfold shortLogLatticeModulus
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  by_cases hsharedZero : shared = 0
  · have hfirstDvd : modulus ∣
        shared * samples.1.1.val + firstPeriod * modulus := by
      rw [hsharedZero, zero_mul, zero_add]
      exact dvd_mul_left _ _
    have hsecondDvd : modulus ∣
        shared * samples.2.1.val + secondPeriod * modulus := by
      rw [hsharedZero, zero_mul, zero_add]
      exact dvd_mul_left _ _
    have hmodulusNatAbs : modulus.natAbs = shortLogLatticeModulus m ell := by
      simp [modulus]
    have hfirstZero :
        shared * samples.1.1.val + firstPeriod * modulus = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hfirstDvd
      rw [hmodulusNatAbs]
      exact hfirst.trans hthresholdLtModulus
    have hsecondZero :
        shared * samples.2.1.val + secondPeriod * modulus = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hsecondDvd
      rw [hmodulusNatAbs]
      exact hsecond.trans hthresholdLtModulus
    apply Prod.ext
    · simpa [shortLogLatticePoint, shared, firstPeriod, modulus,
        hsharedZero] using hfirstZero
    · apply Prod.ext
      · simpa [shortLogLatticePoint, shared, secondPeriod, modulus,
          hsharedZero] using hsecondZero
      · simp [shortLogLatticePoint, shared, hsharedZero]
  · apply False.elim
    apply hclear
    refine ⟨shared.natAbs, Int.natAbs_pos.mpr hsharedZero, ?_, ?_, ?_⟩
    · change coefficients.1.natAbs < 2 ^ (m - 3) at hthird
      simpa [shared, threshold] using hthird
    · have hmodulusPos : 0 < shortLogLatticeModulus m ell := by
        simp [shortLogLatticeModulus]
      rcases Int.natAbs_eq shared with hpositive | hnegative
      · have hvalue :
            ((shared.natAbs * samples.1.1.val : Nat) : Int) =
              shared * (samples.1.1.val : Int) := by
          push_cast
          have habs : |shared| = shared := by
            simpa only [Int.natCast_natAbs] using hpositive.symm
          rw [habs]
        have hmod : Int.ModEq (shortLogLatticeModulus m ell)
            (shared * samples.1.1.val + firstPeriod * modulus)
            (shared.natAbs * samples.1.1.val : Nat) := by
          rw [hvalue]
          simp [modulus]
        exact (NumberTheory.centeredModDistance_le_natAbs_of_intModEq
          hmodulusPos hmod).trans_lt hfirst
      · have hvalue :
            ((shared.natAbs * samples.1.1.val : Nat) : Int) =
              -shared * (samples.1.1.val : Int) := by
          push_cast
          have habs : |shared| = -shared := by
            have h := congrArg Neg.neg hnegative
            simpa only [Int.natCast_natAbs, neg_neg] using h.symm
          rw [habs]
        have hmod : Int.ModEq (shortLogLatticeModulus m ell)
            (-(shared * samples.1.1.val + firstPeriod * modulus))
            (shared.natAbs * samples.1.1.val : Nat) := by
          rw [hvalue]
          simp [modulus, mul_comm, neg_add_rev]
        have hbound := NumberTheory.centeredModDistance_le_natAbs_of_intModEq
          hmodulusPos hmod
        rw [Int.natAbs_neg] at hbound
        exact hbound.trans_lt hfirst
    · have hmodulusPos : 0 < shortLogLatticeModulus m ell := by
        simp [shortLogLatticeModulus]
      rcases Int.natAbs_eq shared with hpositive | hnegative
      · have hvalue :
            ((shared.natAbs * samples.2.1.val : Nat) : Int) =
              shared * (samples.2.1.val : Int) := by
          push_cast
          have habs : |shared| = shared := by
            simpa only [Int.natCast_natAbs] using hpositive.symm
          rw [habs]
        have hmod : Int.ModEq (shortLogLatticeModulus m ell)
            (shared * samples.2.1.val + secondPeriod * modulus)
            (shared.natAbs * samples.2.1.val : Nat) := by
          rw [hvalue]
          simp [modulus]
        exact (NumberTheory.centeredModDistance_le_natAbs_of_intModEq
          hmodulusPos hmod).trans_lt hsecond
      · have hvalue :
            ((shared.natAbs * samples.2.1.val : Nat) : Int) =
              -shared * (samples.2.1.val : Int) := by
          push_cast
          have habs : |shared| = -shared := by
            have h := congrArg Neg.neg hnegative
            simpa only [Int.natCast_natAbs, neg_neg] using h.symm
          rw [habs]
        have hmod : Int.ModEq (shortLogLatticeModulus m ell)
            (-(shared * samples.2.1.val + secondPeriod * modulus))
            (shared.natAbs * samples.2.1.val : Nat) := by
          rw [hvalue]
          simp [modulus, mul_comm, neg_add_rev]
        have hbound := NumberTheory.centeredModDistance_le_natAbs_of_intModEq
          hmodulusPos hmod
        rw [Int.natAbs_neg] at hbound
        exact hbound.trans_lt hsecond

/-- Exact squared form of the corrected source search radius for `s = 2`:
`|u-v| < sqrt(9/8) * 2^m`.

The published PQCrypto 2017 conference version of Ekerå and Håstad,
Sections 3.9–3.10, uses `s/2^4`; the arXiv preprint's `s/4` is a documented
typographical error. -/
def ShortLogNearTarget (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (point : ShortLogLatticePoint) : Prop :=
  8 * NumberTheory.squaredDistance point.toVector
        (shortLogLatticeTarget m ell samples).toVector <
    9 * (2 ^ m) ^ 2

/-- The exact integral search-radius predicate is computationally decidable. -/
instance instDecidableShortLogNearTarget (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (point : ShortLogLatticePoint) :
    Decidable (ShortLogNearTarget m ell samples point) := by
  unfold ShortLogNearTarget
  infer_instance

set_option maxRecDepth 4096 in
/-- Every source-lattice point in the Ekerå–Håstad search ball has reduced
coefficients inside the fixed executable nearest-plane box whenever the
source no-tiny-vector event holds. -/
theorem shortLogReducedCoefficientOffset_mem
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    {point : ShortLogLatticePoint} (hm : 3 ≤ m)
    (hnoTiny : ShortLogNoTinyVector m ell samples)
    (hmember : ShortLogLatticeMember m ell samples point)
    (hnear : ShortLogNearTarget m ell samples point) :
    ∃ coefficients,
      (shortLogRecoveryTrace m ell samples).output.linearCombination
          coefficients = point ∧
        coefficients.sub
            (NumberTheory.IntegerBasis3.nearestPlaneCoefficientCenter
              (shortLogRecoveryTrace m ell samples).output
              (shortLogLatticeTarget m ell samples)) ∈
          NumberTheory.coefficientOffsetBox3
            NumberTheory.nearestPlaneCoefficientBounds3 := by
  let basis := (shortLogRecoveryTrace m ell samples).output
  let target := shortLogLatticeTarget m ell samples
  let threshold : Nat := 2 ^ (m - 3)
  have hfull : basis.FullRank := by
    simpa [basis] using shortLogRecoveryTrace_fullRank m ell samples
  have hreduced : basis.IsReduced := by
    simpa [basis] using shortLogRecoveryTrace_isReduced m ell samples
  have hsourceSpan :
      ∃ coefficients,
        (shortLogLatticeBasis m ell samples).linearCombination coefficients =
          point := by
    rcases hmember with ⟨coefficients, hcoefficients⟩
    refine ⟨coefficients, ?_⟩
    rw [shortLogLatticeBasis_linearCombination]
    exact hcoefficients
  have houtputSpan : ∃ coefficients,
      basis.linearCombination coefficients = point := by
    exact (shortLogRecoveryTrace_spans m ell samples point).mp hsourceSpan
  rcases houtputSpan with ⟨coefficients, hcoefficients⟩
  have hscale : 2 ^ m = 8 * threshold := by
    dsimp [threshold]
    rw [show m = (m - 3) + 3 by omega, pow_add]
    norm_num
    ring
  have hdistanceNat :
      NumberTheory.squaredDistance point.toVector target.toVector <
        72 * threshold ^ 2 := by
    unfold ShortLogNearTarget at hnear
    change 8 * NumberTheory.squaredDistance point.toVector target.toVector <
      9 * (2 ^ m) ^ 2 at hnear
    rw [hscale] at hnear
    nlinarith
  have hdistance :
      (NumberTheory.squaredDistance point.toVector target.toVector : Rat) <
        72 * (threshold ^ 2 : Rat) := by
    exact_mod_cast hdistanceNat
  have hfirstLowerNat : threshold ^ 2 ≤
      NumberTheory.integerPointSquaredNorm basis.first := by
    simpa [basis, threshold] using
      shortLogRecoveryTrace_firstSquaredNorm_lower hnoTiny
  have hfirstLower : (threshold ^ 2 : Rat) ≤
      basis.firstOrthogonalSquaredNorm := by
    unfold NumberTheory.IntegerBasis3.firstOrthogonalSquaredNorm
    exact_mod_cast hfirstLowerNat
  have hthresholdPos : 0 < (threshold ^ 2 : Rat) := by
    positivity
  have hfirstPos : 0 < basis.firstOrthogonalSquaredNorm :=
    hthresholdPos.trans_le hfirstLower
  have hfirstProjection :=
    basis.firstOrthogonalProjection_sq_le_distance hfull point target
  have hfirstDistance :
      (NumberTheory.squaredDistance point.toVector target.toVector : Rat) <
        72 * basis.firstOrthogonalSquaredNorm :=
    hdistance.trans_le
      (mul_le_mul_of_nonneg_left hfirstLower (by norm_num))
  have hfirstSq :
      (basis.firstOrthogonalCoordinate point -
          basis.firstOrthogonalCoordinate target) ^ 2 < 72 := by
    exact lt_of_mul_lt_mul_right
      (hfirstProjection.trans_lt hfirstDistance) hfirstPos.le
  have hfirstProjectionBound :
      |basis.firstOrthogonalCoordinate point -
        basis.firstOrthogonalCoordinate target| < (17 : Rat) / 2 := by
    apply abs_lt_of_sq_lt_sq
    · exact hfirstSq.trans (by norm_num)
    · norm_num
  have hsecondLower := hreduced.secondOrthogonalSquaredNorm_lower hfull
  have hsecondPos : 0 < basis.secondOrthogonalSquaredNorm := by
    have : 0 < basis.firstOrthogonalSquaredNorm / 4 := by positivity
    exact this.trans_le hsecondLower
  have hsecondProjection :=
    basis.secondOrthogonalProjection_sq_le_distance hfull point target
  have hsecondDistance :
      (NumberTheory.squaredDistance point.toVector target.toVector : Rat) <
        288 * basis.secondOrthogonalSquaredNorm := by
    calc
      _ < 72 * (threshold ^ 2 : Rat) := hdistance
      _ ≤ 72 * basis.firstOrthogonalSquaredNorm :=
        mul_le_mul_of_nonneg_left hfirstLower (by norm_num)
      _ = 288 * (basis.firstOrthogonalSquaredNorm / 4) := by ring
      _ ≤ 288 * basis.secondOrthogonalSquaredNorm :=
        mul_le_mul_of_nonneg_left hsecondLower (by norm_num)
  have hsecondSq :
      (basis.secondOrthogonalCoordinate point -
          basis.secondOrthogonalCoordinate target) ^ 2 < 288 := by
    exact lt_of_mul_lt_mul_right
      (hsecondProjection.trans_lt hsecondDistance) hsecondPos.le
  have hsecondProjectionBound :
      |basis.secondOrthogonalCoordinate point -
        basis.secondOrthogonalCoordinate target| < 17 := by
    apply abs_lt_of_sq_lt_sq
    · exact hsecondSq.trans (by norm_num)
    · norm_num
  have hthirdLower :=
    hreduced.thirdOrthogonalSquaredNorm_lower_first hfull
  have hthirdPos : 0 < basis.thirdOrthogonalSquaredNorm := by
    have : 0 < basis.firstOrthogonalSquaredNorm / 16 := by positivity
    exact this.trans_le hthirdLower
  have hthirdProjection :=
    basis.thirdOrthogonalProjection_sq_le_distance hfull point target
  have hthirdDistance :
      (NumberTheory.squaredDistance point.toVector target.toVector : Rat) <
        1152 * basis.thirdOrthogonalSquaredNorm := by
    calc
      _ < 72 * (threshold ^ 2 : Rat) := hdistance
      _ ≤ 72 * basis.firstOrthogonalSquaredNorm :=
        mul_le_mul_of_nonneg_left hfirstLower (by norm_num)
      _ = 1152 * (basis.firstOrthogonalSquaredNorm / 16) := by ring
      _ ≤ 1152 * basis.thirdOrthogonalSquaredNorm :=
        mul_le_mul_of_nonneg_left hthirdLower (by norm_num)
  have hthirdSq :
      (basis.thirdOrthogonalCoordinate point -
          basis.thirdOrthogonalCoordinate target) ^ 2 < 1152 := by
    exact lt_of_mul_lt_mul_right
      (hthirdProjection.trans_lt hthirdDistance) hthirdPos.le
  have hthirdProjectionBound :
      |basis.thirdOrthogonalCoordinate point -
        basis.thirdOrthogonalCoordinate target| < 34 := by
    apply abs_lt_of_sq_lt_sq
    · exact hthirdSq.trans (by norm_num)
    · norm_num
  have hfirstCoefficientProjection :
      |basis.firstOrthogonalCoordinate
          (basis.linearCombination coefficients) -
        basis.firstOrthogonalCoordinate target| < (17 : Rat) / 2 := by
    rw [hcoefficients]
    exact hfirstProjectionBound
  have hsecondCoefficientProjection :
      |basis.secondOrthogonalCoordinate
          (basis.linearCombination coefficients) -
        basis.secondOrthogonalCoordinate target| < 17 := by
    rw [hcoefficients]
    exact hsecondProjectionBound
  have hthirdCoefficientProjection :
      |basis.thirdOrthogonalCoordinate
          (basis.linearCombination coefficients) -
        basis.thirdOrthogonalCoordinate target| < 34 := by
    rw [hcoefficients]
    exact hthirdProjectionBound
  have hfirstOffset := basis.nearestPlaneFirstOffset_abs_lt hfull hreduced
    target coefficients hfirstCoefficientProjection
      hsecondCoefficientProjection hthirdCoefficientProjection
  have hsecondOffset := basis.nearestPlaneSecondOffset_abs_lt hfull hreduced
    target coefficients hsecondCoefficientProjection hthirdCoefficientProjection
  have hthirdOffset := basis.nearestPlaneThirdOffset_abs_lt hfull target
    coefficients hthirdCoefficientProjection
  refine ⟨coefficients, hcoefficients, ?_⟩
  have hoffsetMem :
      coefficients.sub (basis.nearestPlaneCoefficientCenter target) ∈
        NumberTheory.coefficientOffsetBox3
          NumberTheory.nearestPlaneCoefficientBounds3 := by
    exact
      NumberTheory.IntegerBasis3.coefficientOffset_mem_nearestPlaneBox_of_abs_lt
        basis target coefficients hfirstOffset hsecondOffset hthirdOffset
  simpa only [basis, target] using hoffsetMem

/-- A coordinate bound containing the exact source search ball. -/
def shortLogSearchBoxRadius (m : Nat) : Nat :=
  2 ^ (m + 1)

/-- The exact source search ball lies inside the coordinate cube used by the
packing argument.  This theorem now serves only the cardinality proof; the
runtime enumerator works in reduced coefficient space. -/
theorem shortLogNearTarget_mem_searchBox
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    {point : ShortLogLatticePoint}
    (hnear : ShortLogNearTarget m ell samples point) :
    point ∈ NumberTheory.integerCube3 (shortLogLatticeTarget m ell samples)
      (shortLogSearchBoxRadius m) := by
  let target := shortLogLatticeTarget m ell samples
  have hdistance := hnear
  unfold ShortLogNearTarget at hdistance
  change 8 * NumberTheory.squaredDistance point.toVector target.toVector <
    9 * (2 ^ m) ^ 2 at hdistance
  simp only [NumberTheory.squaredDistance_point3] at hdistance
  have hradius : shortLogSearchBoxRadius m = 2 * 2 ^ m := by
    simp [shortLogSearchBoxRadius, pow_succ, mul_comm]
  have hscalePos : 0 < 2 ^ m := by positivity
  have hfirstRadius : (point.1 - target.1).natAbs ≤
      shortLogSearchBoxRadius m := by
    rw [hradius]
    by_contra hnot
    have hgt : 2 * 2 ^ m < (point.1 - target.1).natAbs :=
      Nat.lt_of_not_ge hnot
    nlinarith
  have hsecondRadius : (point.2.1 - target.2.1).natAbs ≤
      shortLogSearchBoxRadius m := by
    rw [hradius]
    by_contra hnot
    have hgt : 2 * 2 ^ m < (point.2.1 - target.2.1).natAbs :=
      Nat.lt_of_not_ge hnot
    nlinarith
  have hthirdRadius : (point.2.2 - target.2.2).natAbs ≤
      shortLogSearchBoxRadius m := by
    rw [hradius]
    by_contra hnot
    have hgt : 2 * 2 ^ m < (point.2.2 - target.2.2).natAbs :=
      Nat.lt_of_not_ge hnot
    nlinarith
  have hfirstUpper := Int.le_natAbs (a := point.1 - target.1)
  have hfirstLower := Int.le_natAbs (a := -(point.1 - target.1))
  have hsecondUpper := Int.le_natAbs (a := point.2.1 - target.2.1)
  have hsecondLower := Int.le_natAbs (a := -(point.2.1 - target.2.1))
  have hthirdUpper := Int.le_natAbs (a := point.2.2 - target.2.2)
  have hthirdLower := Int.le_natAbs (a := -(point.2.2 - target.2.2))
  rw [Int.natAbs_neg] at hfirstLower hsecondLower hthirdLower
  change point ∈ NumberTheory.integerCube3 target
    (shortLogSearchBoxRadius m)
  rw [NumberTheory.mem_integerCube3]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- A conservative constant cap for the number of nearby points in the
three-dimensional `s = 2` search when the source short-vector obstruction is
absent.  The value is `(2 * 2^(m+1) / 2^(m-3) + 1)^3 = 33^3`; the packing
theorem below supplies the connection to the source feasibility event. -/
def shortLogNearbyPointCap : Nat :=
  33 ^ 3

/-- Raw one-dimensional cell index measured from the lower face of the source
search cube in units of `2^(m-3)`. -/
def shortLogPackingIndex (center : Int) (m : Nat)
    (coordinate : Int) : Nat :=
  (coordinate - (center - shortLogSearchBoxRadius m)).toNat / 2 ^ (m - 3)

/-- One coordinate of the fixed `33^3` packing grid used for the source's
three-dimensional `s = 2` recovery analysis.  The final reduction modulo `33`
is definitionally total; the packing proof shows that it is never active on
points in the search cube when `3 ≤ m`. -/
def shortLogPackingCoordinate (center : Int) (m : Nat)
    (coordinate : Int) : Fin 33 :=
  ⟨shortLogPackingIndex center m coordinate % 33,
    Nat.mod_lt _ (by decide)⟩

/-- Every coordinate of the source search cube has a genuine cell index below
`33`; hence the total `Fin 33` encoding does not identify an out-of-range
index with an in-range one. -/
theorem shortLogPackingIndex_lt
    {center coordinate : Int} {m : Nat} (hm : 3 ≤ m)
    (hlower : center - shortLogSearchBoxRadius m ≤ coordinate)
    (hupper : coordinate ≤ center + shortLogSearchBoxRadius m) :
    shortLogPackingIndex center m coordinate < 33 := by
  let offset := coordinate - (center - shortLogSearchBoxRadius m)
  have hoffsetNonneg : 0 ≤ offset := by
    dsimp [offset]
    omega
  have hoffsetUpper : offset ≤ (2 * shortLogSearchBoxRadius m : Nat) := by
    dsimp [offset]
    omega
  have hoffsetNatUpper : offset.toNat ≤ 2 * shortLogSearchBoxRadius m := by
    rw [← Int.ofNat_le]
    simpa [Int.toNat_of_nonneg hoffsetNonneg] using hoffsetUpper
  have hspacingPos : 0 < 2 ^ (m - 3) := Nat.two_pow_pos _
  have hscale : 2 * shortLogSearchBoxRadius m =
      32 * 2 ^ (m - 3) := by
    unfold shortLogSearchBoxRadius
    rw [show m + 1 = (m - 3) + 4 by omega, pow_add]
    ring
  unfold shortLogPackingIndex
  rw [Nat.div_lt_iff_lt_mul hspacingPos]
  exact hoffsetNatUpper.trans_lt (by rw [hscale]; omega)

/-- Two in-cube coordinates with the same packing address differ by strictly
less than the source short-vector threshold `2^(m-3)`. -/
theorem natAbs_sub_lt_of_shortLogPackingCoordinate_eq
    {center left right : Int} {m : Nat} (hm : 3 ≤ m)
    (hleftLower : center - shortLogSearchBoxRadius m ≤ left)
    (hleftUpper : left ≤ center + shortLogSearchBoxRadius m)
    (hrightLower : center - shortLogSearchBoxRadius m ≤ right)
    (hrightUpper : right ≤ center + shortLogSearchBoxRadius m)
    (haddress : shortLogPackingCoordinate center m left =
      shortLogPackingCoordinate center m right) :
    (left - right).natAbs < 2 ^ (m - 3) := by
  let lower : Int := center - shortLogSearchBoxRadius m
  let leftOffset : Int := left - lower
  let rightOffset : Int := right - lower
  have hleftNonneg : 0 ≤ leftOffset := by
    dsimp [leftOffset, lower]
    omega
  have hrightNonneg : 0 ≤ rightOffset := by
    dsimp [rightOffset, lower]
    omega
  have hleftIndex := shortLogPackingIndex_lt hm hleftLower hleftUpper
  have hrightIndex := shortLogPackingIndex_lt hm hrightLower hrightUpper
  have hquotient : leftOffset.toNat / 2 ^ (m - 3) =
      rightOffset.toNat / 2 ^ (m - 3) := by
    have hvalue := congrArg Fin.val haddress
    change shortLogPackingIndex center m left % 33 =
      shortLogPackingIndex center m right % 33 at hvalue
    rw [Nat.mod_eq_of_lt hleftIndex, Nat.mod_eq_of_lt hrightIndex] at hvalue
    simpa [shortLogPackingIndex, leftOffset, rightOffset, lower] using hvalue
  have hdist := NumberTheory.natDist_lt_of_div_eq
    (Nat.two_pow_pos (m - 3)) hquotient
  have habs : (leftOffset - rightOffset).natAbs =
      Nat.dist leftOffset.toNat rightOffset.toNat :=
    NumberTheory.natAbs_sub_eq_natDist_toNat hleftNonneg hrightNonneg
  have hoffsetSub : leftOffset - rightOffset = left - right := by
    dsimp [leftOffset, rightOffset, lower]
    ring
  rw [hoffsetSub] at habs
  exact habs.trans_lt hdist

/-- Three-coordinate packing address of a searched lattice point. -/
def shortLogPackingAddress (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (point : ShortLogLatticePoint) : Fin 33 × Fin 33 × Fin 33 :=
  (shortLogPackingCoordinate (shortLogLatticeTarget m ell samples).1 m
      point.1,
    shortLogPackingCoordinate (shortLogLatticeTarget m ell samples).2.1 m
      point.2.1,
    shortLogPackingCoordinate (shortLogLatticeTarget m ell samples).2.2 m
      point.2.2)

/-- A searched lattice point whose last coordinate is a range-valid public
short logarithm.  Validation is intrinsic to the public generator and target;
no secret or caller decoder is accepted. -/
def ShortLogValidatedPoint {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (point : ShortLogLatticePoint) : Prop :=
  ShortLogLatticeMember m ell samples point ∧
    ShortLogNearTarget m ell samples point ∧
    0 < point.2.2 ∧ point.2.2 < (2 ^ m : Nat) ∧
    generator ^ point.2.2.toNat = targetUnit generator

/-- Small integral squared-radius envelope used by the coefficient enumerator.
The outer exact filter below restores the corrected strict `8/9` inequality. -/
def shortLogEnumerationRadiusSquared (m : Nat) : Nat :=
  2 * (2 ^ m) ^ 2

/-- Executable reduced-basis enumeration of the actual source search ball.
It inspects a fixed coefficient box around the exact nearest-plane center and
then applies the corrected conference radius predicate `8D < 9B²`. -/
def shortLogNearLatticePoints (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    Finset ShortLogLatticePoint :=
  (NumberTheory.enumerateNearbyPoints3
    (shortLogRecoveryTrace m ell samples).output
    (shortLogLatticeTarget m ell samples)
    (shortLogEnumerationRadiusSquared m)
    (NumberTheory.IntegerBasis3.nearestPlaneCoefficientCenter
      (shortLogRecoveryTrace m ell samples).output
      (shortLogLatticeTarget m ell samples))
    NumberTheory.nearestPlaneCoefficientBounds3).filter fun point =>
      8 * NumberTheory.squaredDistance point.toVector
          (shortLogLatticeTarget m ell samples).toVector <
        9 * (2 ^ m) ^ 2

section ExecutableShortLogRecovery

set_option maxRecDepth 3000

/-- Every enumerated point satisfies the exact source near-target predicate. -/
theorem shortLogNearLatticePoints_near
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    {point : ShortLogLatticePoint}
    (hpoint : point ∈ shortLogNearLatticePoints m ell samples) :
    ShortLogNearTarget m ell samples point := by
  rw [shortLogNearLatticePoints, Finset.mem_filter] at hpoint
  exact hpoint.2

/-- Every enumerated point belongs to the original source row-span lattice;
this follows from the certified lattice equality of the LLL trace. -/
theorem shortLogNearLatticePoints_member
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    {point : ShortLogLatticePoint}
    (hpoint : point ∈ shortLogNearLatticePoints m ell samples) :
    ShortLogLatticeMember m ell samples point := by
  rw [shortLogNearLatticePoints, Finset.mem_filter] at hpoint
  have henumerated := hpoint.1
  have hrepresentation :=
    (NumberTheory.mem_enumerateNearbyPoints3.mp henumerated).2
  rcases hrepresentation with ⟨offset, _hoffset, hpointEq⟩
  have houtputSpan : ∃ coefficients,
      (shortLogRecoveryTrace m ell samples).output.linearCombination
          coefficients = point :=
    ⟨(NumberTheory.IntegerPoint3.add
        (NumberTheory.IntegerBasis3.nearestPlaneCoefficientCenter
          (shortLogRecoveryTrace m ell samples).output
          (shortLogLatticeTarget m ell samples)) offset),
      hpointEq⟩
  have hsourceSpan :=
    (shortLogRecoveryTrace_spans m ell samples point).mpr houtputSpan
  rcases hsourceSpan with ⟨coefficients, hcoefficients⟩
  rw [shortLogLatticeBasis_linearCombination] at hcoefficients
  exact ⟨coefficients, hcoefficients⟩

/-- Under the source no-tiny-vector event, every source-lattice point in the
exact search ball occurs in the executable nearest-plane enumeration. -/
theorem shortLogNearLatticePoints_complete
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    {point : ShortLogLatticePoint} (hm : 3 ≤ m)
    (hnoTiny : ShortLogNoTinyVector m ell samples)
    (hmember : ShortLogLatticeMember m ell samples point)
    (hnear : ShortLogNearTarget m ell samples point) :
    point ∈ shortLogNearLatticePoints m ell samples := by
  rcases shortLogReducedCoefficientOffset_mem hm hnoTiny hmember hnear with
    ⟨coefficients, hcoefficients, hoffset⟩
  rw [shortLogNearLatticePoints, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [NumberTheory.mem_enumerateNearbyPoints3]
    constructor
    · unfold NumberTheory.IsInsideSquaredBall shortLogEnumerationRadiusSquared
      unfold ShortLogNearTarget at hnear
      omega
    · let center := NumberTheory.IntegerBasis3.nearestPlaneCoefficientCenter
          (shortLogRecoveryTrace m ell samples).output
          (shortLogLatticeTarget m ell samples)
      let offset := coefficients.sub center
      refine ⟨offset, ?_, ?_⟩
      · simpa [offset, center] using hoffset
      · have hcenter : center.add offset = coefficients := by
          apply Prod.ext
          · simp [center, offset, NumberTheory.IntegerPoint3.add,
              NumberTheory.IntegerPoint3.sub]
          · apply Prod.ext <;>
              simp [center, offset, NumberTheory.IntegerPoint3.add,
                NumberTheory.IntegerPoint3.sub]
        rw [hcenter]
        exact hcoefficients
  · exact hnear

/-- Proof-side recovery certificate: the source no-tiny-vector event holds and
the resulting complete executable neighborhood satisfies the constant packing
cap [EH17, source.tex:737-776].  The runtime does not branch on this `Prop`. -/
def ShortLogRecoveryFeasible (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) : Prop :=
  3 ≤ m ∧ ShortLogNoTinyVector m ell samples ∧
    (shortLogNearLatticePoints m ell samples).card ≤
      shortLogNearbyPointCap

/-- Source-shaped separation event: distinct nearby lattice points occupy
distinct cells of the fixed packing grid.  This is the deterministic bridge
between the short-vector event and the executable enumeration cap. -/
def ShortLogPackingSeparated (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) : Prop :=
  Set.InjOn (shortLogPackingAddress m ell samples)
    (shortLogNearLatticePoints m ell samples)

/-- A separated packing makes the complete finite lattice search satisfy the
same constant cap tested by the recovery implementation. -/
theorem shortLogRecoveryFeasible_of_packingSeparated
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hm : 3 ≤ m)
    (hnoTiny : ShortLogNoTinyVector m ell samples)
    (hseparated : ShortLogPackingSeparated m ell samples) :
    ShortLogRecoveryFeasible m ell samples := by
  have hcard : (shortLogNearLatticePoints m ell samples).card ≤
      (Finset.univ : Finset (Fin 33 × Fin 33 × Fin 33)).card :=
    Finset.card_le_card_of_injOn (shortLogPackingAddress m ell samples)
      (fun _point _hpoint => Finset.mem_univ _) hseparated
  refine ⟨hm, hnoTiny, ?_⟩
  simpa [shortLogNearbyPointCap, pow_succ] using hcard

/-- The source no-short-vector event forces packing separation of every point
that the executable geometric search can inspect. -/
theorem shortLogPackingSeparated_of_noTinyVector
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hm : 3 ≤ m) (hnoTiny : ShortLogNoTinyVector m ell samples) :
    ShortLogPackingSeparated m ell samples := by
  classical
  intro left hleft right hright haddress
  change left ∈ shortLogNearLatticePoints m ell samples at hleft
  change right ∈ shortLogNearLatticePoints m ell samples at hright
  have hleftNear := shortLogNearLatticePoints_near hleft
  have hrightNear := shortLogNearLatticePoints_near hright
  have hleftBounds := NumberTheory.mem_integerCube3.mp
    (shortLogNearTarget_mem_searchBox hleftNear)
  have hrightBounds := NumberTheory.mem_integerCube3.mp
    (shortLogNearTarget_mem_searchBox hrightNear)
  have hfirstAddress := congrArg Prod.fst haddress
  have hsecondAddress := congrArg (fun address => address.2.1) haddress
  have hthirdAddress := congrArg (fun address => address.2.2) haddress
  have hfirstTiny : (left.1 - right.1).natAbs < 2 ^ (m - 3) :=
    natAbs_sub_lt_of_shortLogPackingCoordinate_eq hm
      hleftBounds.1 hleftBounds.2.1 hrightBounds.1 hrightBounds.2.1
      hfirstAddress
  have hsecondTiny : (left.2.1 - right.2.1).natAbs < 2 ^ (m - 3) :=
    natAbs_sub_lt_of_shortLogPackingCoordinate_eq hm
      hleftBounds.2.2.1 hleftBounds.2.2.2.1
      hrightBounds.2.2.1 hrightBounds.2.2.2.1 hsecondAddress
  have hthirdTiny : (left.2.2 - right.2.2).natAbs < 2 ^ (m - 3) :=
    natAbs_sub_lt_of_shortLogPackingCoordinate_eq hm
      hleftBounds.2.2.2.2.1 hleftBounds.2.2.2.2.2
      hrightBounds.2.2.2.2.1 hrightBounds.2.2.2.2.2 hthirdAddress
  have hmember : ShortLogLatticeMember m ell samples
      (shortLogLatticePointSub left right) :=
    ShortLogLatticeMember.sub
      (shortLogNearLatticePoints_member hleft)
      (shortLogNearLatticePoints_member hright)
  have hzero := hnoTiny (shortLogLatticePointSub left right) hmember
    hfirstTiny hsecondTiny hthirdTiny
  apply Prod.ext
  · exact sub_eq_zero.mp <| by
      simpa [shortLogLatticePointSub] using congrArg Prod.fst hzero
  · apply Prod.ext
    · exact sub_eq_zero.mp <| by
        simpa [shortLogLatticePointSub] using
          congrArg (fun point => point.2.1) hzero
    · exact sub_eq_zero.mp <| by
        simpa [shortLogLatticePointSub] using
          congrArg (fun point => point.2.2) hzero

/-- Source no-short-vector feasibility theorem consumed by the closed
recovery implementation. -/
theorem shortLogRecoveryFeasible_of_noTinyVector
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hm : 3 ≤ m) (hnoTiny : ShortLogNoTinyVector m ell samples) :
    ShortLogRecoveryFeasible m ell samples :=
  shortLogRecoveryFeasible_of_packingSeparated hm hnoTiny
    (shortLogPackingSeparated_of_noTinyVector hm hnoTiny)

/-- Centered distance of `d*j + 2^m*k` modulo `2^(m+ell)`. -/
def shortLogCenteredDistance (m ell secret : Nat)
    (sample : ShortLogSample m ell) : Nat :=
  NumberTheory.centeredModDistance (2 ^ (ell + m))
    (secret * sample.1.val + 2 ^ m * sample.2.val)

/-- The source good-pair window for the `s = 2` tradeoff.

The threshold is the literal `2^(m-2)` condition used before the lattice
recovery argument [EH17, source.tex:515-537]. -/
def ShortLogGoodSample (m ell secret : Nat)
    (sample : ShortLogSample m ell) : Prop :=
  shortLogCenteredDistance m ell secret sample ≤ 2 ^ (m - 2)

/-- The source lattice point determined by a proposed short logarithm and the
two centered measurement errors. -/
def shortLogWitnessPoint (m ell secret : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    ShortLogLatticePoint :=
  (shortLogTargetCoordinate m ell samples.1 +
      shortLogErrorCoordinate m ell secret samples.1,
    shortLogTargetCoordinate m ell samples.2 +
      shortLogErrorCoordinate m ell secret samples.2,
    secret)

/-- The centered witness is an actual point of the source row-span lattice. -/
theorem shortLogWitnessPoint_mem (m ell secret : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    ShortLogLatticeMember m ell samples
      (shortLogWitnessPoint m ell secret samples) := by
  let modulus := shortLogLatticeModulus m ell
  have hmodulus : 0 < modulus := by
    simp [modulus, shortLogLatticeModulus]
  have firstTarget : Int.ModEq modulus
      (shortLogTargetCoordinate m ell samples.1)
      (-(2 ^ m * samples.1.2.val : Nat) : Int) := by
    exact (NumberTheory.centeredResidue_modEq modulus
      (NumberTheory.modularNegation modulus
        (2 ^ m * samples.1.2.val))).trans
      (NumberTheory.modularNegation_modEq_neg hmodulus)
  have firstError : Int.ModEq modulus
      (shortLogErrorCoordinate m ell secret samples.1)
      (secret * samples.1.1.val + 2 ^ m * samples.1.2.val : Nat) :=
    NumberTheory.centeredResidue_modEq modulus _
  have firstCoordinate : Int.ModEq modulus
      (shortLogTargetCoordinate m ell samples.1 +
        shortLogErrorCoordinate m ell secret samples.1)
      (secret * samples.1.1.val : Nat) := by
    have combined := firstTarget.add firstError
    push_cast at combined ⊢
    convert combined using 1
    all_goals ring
  have secondTarget : Int.ModEq modulus
      (shortLogTargetCoordinate m ell samples.2)
      (-(2 ^ m * samples.2.2.val : Nat) : Int) := by
    exact (NumberTheory.centeredResidue_modEq modulus
      (NumberTheory.modularNegation modulus
        (2 ^ m * samples.2.2.val))).trans
      (NumberTheory.modularNegation_modEq_neg hmodulus)
  have secondError : Int.ModEq modulus
      (shortLogErrorCoordinate m ell secret samples.2)
      (secret * samples.2.1.val + 2 ^ m * samples.2.2.val : Nat) :=
    NumberTheory.centeredResidue_modEq modulus _
  have secondCoordinate : Int.ModEq modulus
      (shortLogTargetCoordinate m ell samples.2 +
        shortLogErrorCoordinate m ell secret samples.2)
      (secret * samples.2.1.val : Nat) := by
    have combined := secondTarget.add secondError
    push_cast at combined ⊢
    convert combined using 1
    all_goals ring
  rcases Int.modEq_iff_add_fac.mp firstCoordinate with
    ⟨firstPeriod, hfirstPeriod⟩
  rcases Int.modEq_iff_add_fac.mp secondCoordinate with
    ⟨secondPeriod, hsecondPeriod⟩
  refine ⟨((secret : Int), -firstPeriod, -secondPeriod), ?_⟩
  apply Prod.ext
  · dsimp [shortLogLatticePoint, shortLogWitnessPoint]
    have := hfirstPeriod
    push_cast at this
    rw [show (shortLogLatticeModulus m ell : Int) = modulus by rfl]
    rw [this]
    ring
  · apply Prod.ext
    · dsimp [shortLogLatticePoint, shortLogWitnessPoint]
      have := hsecondPeriod
      push_cast at this
      rw [show (shortLogLatticeModulus m ell : Int) = modulus by rfl]
      rw [this]
      ring
    · simp [shortLogLatticePoint, shortLogWitnessPoint]

/-- Two source-good measurements place the hidden-log witness strictly inside
the corrected `s = 2` search ball.

The good-pair window is [EH17, source.tex:515-537]; the `s/2^4` radius is the
correction published in Ekerå and Håstad's PQCrypto 2017 conference version,
Sections 3.9–3.10. -/
theorem shortLogWitnessPoint_near_of_good
    {m ell secret : Nat}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hsecretPos : 0 < secret) (hsecretLt : secret < 2 ^ m)
    (hfirst : ShortLogGoodSample m ell secret samples.1)
    (hsecond : ShortLogGoodSample m ell secret samples.2) :
    ShortLogNearTarget m ell samples
      (shortLogWitnessPoint m ell secret samples) := by
  have hmPos : 0 < m := by
    by_contra hm
    have hmZero : m = 0 := Nat.eq_zero_of_not_pos hm
    simp [hmZero] at hsecretLt
    omega
  have hmodulus : 0 < shortLogLatticeModulus m ell := by
    simp [shortLogLatticeModulus]
  have hfirstAbs :
      (shortLogErrorCoordinate m ell secret samples.1).natAbs =
        shortLogCenteredDistance m ell secret samples.1 := by
    exact NumberTheory.natAbs_centeredResidue hmodulus
  have hsecondAbs :
      (shortLogErrorCoordinate m ell secret samples.2).natAbs =
        shortLogCenteredDistance m ell secret samples.2 := by
    exact NumberTheory.natAbs_centeredResidue hmodulus
  have hfirstQuarter :
      (shortLogErrorCoordinate m ell secret samples.1).natAbs ≤
        2 ^ (m - 2) := by
    rw [hfirstAbs]
    exact hfirst
  have hsecondQuarter :
      (shortLogErrorCoordinate m ell secret samples.2).natAbs ≤
        2 ^ (m - 2) := by
    rw [hsecondAbs]
    exact hsecond
  have hfirstSq :
      (shortLogErrorCoordinate m ell secret samples.1).natAbs ^ 2 ≤
        (2 ^ (m - 2)) ^ 2 :=
    Nat.pow_le_pow_left hfirstQuarter 2
  have hsecondSq :
      (shortLogErrorCoordinate m ell secret samples.2).natAbs ^ 2 ≤
        (2 ^ (m - 2)) ^ 2 :=
    Nat.pow_le_pow_left hsecondQuarter 2
  have hsecretSq : secret ^ 2 < (2 ^ m) ^ 2 :=
    Nat.pow_lt_pow_left hsecretLt (by norm_num)
  unfold ShortLogNearTarget
  simp only [shortLogWitnessPoint, shortLogLatticeTarget,
    NumberTheory.squaredDistance_point3, add_sub_cancel_left,
    Int.natAbs_natCast, Int.sub_zero]
  norm_num [pow_two] at hfirstSq hsecondSq hsecretSq ⊢
  by_cases hmTwo : 2 ≤ m
  · have hquarter : 4 * 2 ^ (m - 2) = 2 ^ m := by
      calc
        4 * 2 ^ (m - 2) = 2 ^ 2 * 2 ^ (m - 2) := by norm_num
        _ = 2 ^ (2 + (m - 2)) := by rw [pow_add]
        _ = 2 ^ m := by
          congr 1
          omega
    nlinarith [hquarter]
  · have hmOne : m = 1 := by omega
    subst m
    norm_num at hfirstSq hsecondSq hsecretSq ⊢
    nlinarith

/-- A value accepted by the closed two-sample recovery semantics.  It must be
the public target logarithm and both measured pairs must satisfy the exact
source good-pair window.  This is the semantic specification of the `s = 2`
lattice-neighborhood search: the lattice is [EH17, source.tex:675-696], the
good-pair window is [EH17, source.tex:515-537], and the corrected radius is in
the PQCrypto 2017 conference version, Sections 3.9–3.10. -/
def ShortLogPairCandidate {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (secret : Nat) : Prop :=
  0 < secret ∧ secret < 2 ^ m ∧
    generator ^ secret = targetUnit generator ∧
    ShortLogGoodSample m ell secret samples.1 ∧
    ShortLogGoodSample m ell secret samples.2

section SealedPairArithmetic

/-- A value together with the operand-derived arithmetic emitted while
computing that same value inside one short-log recovery execution. -/
private structure ShortLogArithmeticExecution (α : Type) where
  value : α
  arithmetic : List NumberTheory.ArithmeticEvent

private def shortLogIntAddExecution (left right : Int) :
    ShortLogArithmeticExecution Int :=
  { value := left + right
    arithmetic := [.intAdd left right] }

private def shortLogIntSubExecution (left right : Int) :
    ShortLogArithmeticExecution Int :=
  { value := left - right
    arithmetic := [.intSub left right] }

private def shortLogIntMulExecution (left right : Int) :
    ShortLogArithmeticExecution Int :=
  { value := left * right
    arithmetic := [.intMul left right] }

private def shortLogNatAddExecution (left right : Nat) :
    ShortLogArithmeticExecution Nat :=
  { value := left + right
    arithmetic := [.natAdd left right] }

private def shortLogNatSubExecution (left right : Nat) :
    ShortLogArithmeticExecution Nat :=
  { value := left - right
    arithmetic := [.natSub left right] }

private def shortLogNatMulExecution (left right : Nat) :
    ShortLogArithmeticExecution Nat :=
  { value := left * right
    arithmetic := [.natMul left right] }

/-- Coordinatewise addition used to form one coefficient tuple around the
single nearest-plane center owned by the pair trace. -/
private def shortLogPointAddExecution
    (left right : NumberTheory.IntegerPoint3) :
    ShortLogArithmeticExecution NumberTheory.IntegerPoint3 :=
  let first := shortLogIntAddExecution left.1 right.1
  let second := shortLogIntAddExecution left.2.1 right.2.1
  let third := shortLogIntAddExecution left.2.2 right.2.2
  { value := (first.value, second.value, third.value)
    arithmetic := first.arithmetic ++ second.arithmetic ++ third.arithmetic }

/-- Evaluate all nine scalar products and all six additions in one
three-dimensional basis linear combination. -/
private def shortLogLinearCombinationExecution
    (basis : NumberTheory.IntegerBasis3)
    (coefficients : NumberTheory.IntegerPoint3) :
    ShortLogArithmeticExecution NumberTheory.IntegerPoint3 :=
  let firstFirst := shortLogIntMulExecution coefficients.1 basis.first.1
  let firstSecond := shortLogIntMulExecution coefficients.1 basis.first.2.1
  let firstThird := shortLogIntMulExecution coefficients.1 basis.first.2.2
  let secondFirst := shortLogIntMulExecution coefficients.2.1 basis.second.1
  let secondSecond := shortLogIntMulExecution coefficients.2.1 basis.second.2.1
  let secondThird := shortLogIntMulExecution coefficients.2.1 basis.second.2.2
  let thirdFirst := shortLogIntMulExecution coefficients.2.2 basis.third.1
  let thirdSecond := shortLogIntMulExecution coefficients.2.2 basis.third.2.1
  let thirdThird := shortLogIntMulExecution coefficients.2.2 basis.third.2.2
  let tailFirst := shortLogIntAddExecution secondFirst.value thirdFirst.value
  let tailSecond := shortLogIntAddExecution secondSecond.value thirdSecond.value
  let tailThird := shortLogIntAddExecution secondThird.value thirdThird.value
  let outputFirst := shortLogIntAddExecution firstFirst.value tailFirst.value
  let outputSecond := shortLogIntAddExecution firstSecond.value tailSecond.value
  let outputThird := shortLogIntAddExecution firstThird.value tailThird.value
  { value := (outputFirst.value, outputSecond.value, outputThird.value)
    arithmetic :=
      firstFirst.arithmetic ++ firstSecond.arithmetic ++
      firstThird.arithmetic ++ secondFirst.arithmetic ++
      secondSecond.arithmetic ++ secondThird.arithmetic ++
      thirdFirst.arithmetic ++ thirdSecond.arithmetic ++
      thirdThird.arithmetic ++ tailFirst.arithmetic ++
      tailSecond.arithmetic ++ tailThird.arithmetic ++
      outputFirst.arithmetic ++ outputSecond.arithmetic ++
      outputThird.arithmetic }

/-- Compute the lattice point at one offset from the already-computed shared
nearest-plane center. -/
private def shortLogPointAtOffsetExecution
    (basis : NumberTheory.IntegerBasis3)
    (center offset : NumberTheory.IntegerPoint3) :
    ShortLogArithmeticExecution ShortLogLatticePoint :=
  let coefficients := shortLogPointAddExecution center offset
  let point := shortLogLinearCombinationExecution basis coefficients.value
  { value := point.value
    arithmetic := coefficients.arithmetic ++ point.arithmetic }

/-- The audited point execution computes the mathematical basis combination
at the supplied center and offset. -/
private theorem shortLogPointAtOffsetExecution_value
    (basis : NumberTheory.IntegerBasis3)
    (center offset : NumberTheory.IntegerPoint3) :
    (shortLogPointAtOffsetExecution basis center offset).value =
      basis.linearCombination (center.add offset) := by
  rfl

/-- Canonical point projection from a shared nearest-plane trace. -/
private def shortLogCandidatePointFromCommon (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (reduction : NumberTheory.LatticeReductionTrace3)
    (nearest : NumberTheory.NearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples))
    (offset : NumberTheory.IntegerPoint3) : ShortLogLatticePoint :=
  (shortLogPointAtOffsetExecution reduction.output nearest.center offset).value

/-- Every coefficient in the canonical fixed scan satisfies its
coordinate-specific corrected-radius bound. -/
private theorem shortLogCoefficientOffset_coordinates_le
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3) :
    offset.1.natAbs ≤ 42 ∧ offset.2.1.natAbs ≤ 34 ∧
      offset.2.2.natAbs ≤ 34 := by
  rw [NumberTheory.mem_coefficientOffsetList3,
    NumberTheory.mem_coefficientOffsetBox3] at hoffset
  simp only [NumberTheory.nearestPlaneCoefficientBounds3] at hoffset
  have coordinate_le (radius : Nat) (value : Int)
      (hlower : -(radius : Int) ≤ value)
      (hupper : value ≤ (radius : Int)) :
      value.natAbs ≤ radius := by
    have hcast : (value.natAbs : Int) ≤ (radius : Int) := by
      rcases Int.natAbs_eq value with hpositive | hnegative
      · rw [hpositive] at hupper
        exact hupper
      · rw [hnegative] at hlower
        omega
    exact_mod_cast hcast
  exact
    ⟨coordinate_le 42 offset.1 hoffset.1 hoffset.2.1,
      coordinate_le 34 offset.2.1 hoffset.2.2.1 hoffset.2.2.2.1,
      coordinate_le 34 offset.2.2 hoffset.2.2.2.2.1
        hoffset.2.2.2.2.2⟩

/-- Magnitude envelope for every actual lattice point generated by the
canonical coefficient scan. -/
private def shortLogCandidatePointMagnitude (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) : Nat :=
  3 * (shortLogNearestPlaneOperandMagnitude m ell samples + 43) *
    (shortLogReducedBasisBound m ell samples + 1)

/-- The canonical candidate-point magnitude has linear binary size in the
public short-log input envelope. -/
private theorem shortLogCandidatePointMagnitude_size_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    Nat.size (shortLogCandidatePointMagnitude m ell samples) ≤
      512 * shortLogRecoveryInputBits N m ell := by
  let centerBound := shortLogNearestPlaneOperandMagnitude m ell samples
  let basisBound := shortLogReducedBasisBound m ell samples
  let inputBits := shortLogRecoveryInputBits N m ell
  have hinputBitsPos : 1 ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hcenterSize : Nat.size centerBound ≤ 256 * inputBits := by
    exact (Nat.le_add_right _ 1).trans
      (by
        simpa [centerBound, inputBits] using
          shortLogNearestPlaneOperandMagnitude_size_succ_le
            N m ell samples)
  have hcenterPos : 1 ≤ centerBound := by
    have hpositive : 0 < centerBound := by
      dsimp only [centerBound, shortLogNearestPlaneOperandMagnitude,
        shortLogReducedBasisBound, shortLogLatticeModulus]
      positivity
    exact hpositive
  have hcenterSucc : centerBound + 43 ≤ 44 * centerBound := by
    omega
  have hcenterSuccSize : Nat.size (centerBound + 43) ≤
      6 + 256 * inputBits := by
    have hsize44 : Nat.size 44 = 6 := by decide
    calc
      Nat.size (centerBound + 43) ≤ Nat.size (44 * centerBound) :=
        Nat.size_le_size hcenterSucc
      _ ≤ Nat.size 44 + Nat.size centerBound :=
        NumberTheory.natSize_mul_le_add _ _
      _ ≤ Nat.size 44 + 256 * inputBits :=
        Nat.add_le_add_left hcenterSize _
      _ = 6 + 256 * inputBits := by rw [hsize44]
  have hbasisSize : Nat.size (basisBound + 1) ≤ 22 * inputBits := by
    let source := shortLogLatticeBasis m ell samples
    have hsourceInput : source.inputBitSize ≤ 2 * (ell + m) + 3 := by
      simpa [source] using shortLogLatticeBasis_inputBitSize_le m ell samples
    have hsucc : Nat.size (basisBound + 1) ≤
        12 * (ell + m) + 22 := by
      calc
        Nat.size (basisBound + 1) ≤ 4 + 6 * source.inputBitSize := by
          simpa [basisBound, shortLogReducedBasisBound, source] using
            NumberTheory.lllStateEnvelope3_succ_size_le source
        _ ≤ 4 + 6 * (2 * (ell + m) + 3) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 6 hsourceInput) 4
        _ = 12 * (ell + m) + 22 := by ring
    calc
      Nat.size (basisBound + 1) ≤ 12 * (ell + m) + 22 := hsucc
      _ ≤ 22 * inputBits := by
        dsimp only [inputBits, shortLogRecoveryInputBits]
        omega
  have hsizeThree : Nat.size 3 = 2 := by decide
  calc
    Nat.size (shortLogCandidatePointMagnitude m ell samples) =
        Nat.size ((3 * (centerBound + 43)) * (basisBound + 1)) := by
      simp only [shortLogCandidatePointMagnitude, centerBound, basisBound]
    _ ≤ Nat.size (3 * (centerBound + 43)) + Nat.size (basisBound + 1) :=
      NumberTheory.natSize_mul_le_add _ _
    _ ≤ (Nat.size 3 + Nat.size (centerBound + 43)) +
        Nat.size (basisBound + 1) :=
      Nat.add_le_add_right
        (NumberTheory.natSize_mul_le_add 3 (centerBound + 43)) _
    _ ≤ (Nat.size 3 + (6 + 256 * inputBits)) + 22 * inputBits :=
      Nat.add_le_add
        (Nat.add_le_add_left hcenterSuccSize _)
        hbasisSize
    _ ≤ 512 * inputBits := by
      rw [hsizeThree]
      omega

/-- Every actual point produced by the canonical scan satisfies the shared
input-derived coordinate envelope. -/
private theorem shortLogCandidatePointFromCommon_coordinates_le
    (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3) :
    let reduction := shortLogRecoveryTrace m ell samples
    let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples)
    let point := shortLogCandidatePointFromCommon m ell samples reduction
      nearest offset
    point.1.natAbs ≤ shortLogCandidatePointMagnitude m ell samples ∧
      point.2.1.natAbs ≤ shortLogCandidatePointMagnitude m ell samples ∧
      point.2.2.natAbs ≤ shortLogCandidatePointMagnitude m ell samples := by
  let reduction := shortLogRecoveryTrace m ell samples
  let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
    (shortLogLatticeTarget m ell samples)
  let basisBound := shortLogReducedBasisBound m ell samples
  let centerBound := shortLogNearestPlaneOperandMagnitude m ell samples
  have hfull : reduction.output.FullRank := by
    simpa [reduction] using shortLogRecoveryTrace_fullRank m ell samples
  have hbasis : reduction.output.SquaredNormsLe basisBound := by
    simpa [reduction, basisBound, shortLogReducedBasisBound,
      shortLogRecoveryTrace] using
      (NumberTheory.lllReduce3WithFuel_output_squaredNormsLe
        (shortLogRecoveryFuel m ell) (shortLogLatticeBasis m ell samples)
        (shortLogLatticeBasis_fullRank m ell samples))
  have htarget : NumberTheory.integerPointSquaredNorm
      (shortLogLatticeTarget m ell samples) ≤
        2 * shortLogLatticeModulus m ell ^ 2 :=
    shortLogLatticeTarget_squaredNorm_le m ell samples
  have hcenter : nearest.center.1.natAbs ≤ centerBound ∧
      nearest.center.2.1.natAbs ≤ centerBound ∧
      nearest.center.2.2.natAbs ≤ centerBound := by
    simpa [nearest, reduction, centerBound,
      shortLogNearestPlaneOperandMagnitude, basisBound,
      shortLogReducedBasisBound] using
      (NumberTheory.nearestPlaneTrace3_center_coordinates_le
        reduction.output (shortLogLatticeTarget m ell samples)
        basisBound (2 * shortLogLatticeModulus m ell ^ 2)
        hfull hbasis htarget)
  have hoffsetBound := shortLogCoefficientOffset_coordinates_le hoffset
  have hcoefficients :
      (nearest.center.add offset).1.natAbs ≤ centerBound + 42 ∧
        (nearest.center.add offset).2.1.natAbs ≤ centerBound + 42 ∧
        (nearest.center.add offset).2.2.natAbs ≤ centerBound + 42 := by
    simp only [NumberTheory.IntegerPoint3.add]
    exact
      ⟨(Int.natAbs_add_le _ _).trans
          (Nat.add_le_add hcenter.1 hoffsetBound.1),
        (Int.natAbs_add_le _ _).trans
          ((Nat.add_le_add hcenter.2.1 hoffsetBound.2.1).trans (by omega)),
        (Int.natAbs_add_le _ _).trans
          ((Nat.add_le_add hcenter.2.2 hoffsetBound.2.2).trans (by omega))⟩
  have hpoint := NumberTheory.IntegerBasis3.linearCombination_coordinates_le
    reduction.output (nearest.center.add offset) basisBound
      (centerBound + 42) hbasis hcoefficients
  dsimp only
  rw [shortLogCandidatePointFromCommon,
    shortLogPointAtOffsetExecution_value]
  have henvelope : 3 * (centerBound + 42) * basisBound ≤
      shortLogCandidatePointMagnitude m ell samples := by
    simp only [shortLogCandidatePointMagnitude, centerBound, basisBound]
    nlinarith
  exact
    ⟨hpoint.1.trans henvelope,
      hpoint.2.1.trans henvelope,
      hpoint.2.2.trans henvelope⟩

/-- Every candidate exponent extracted from the canonical coefficient scan
has width linear in the public short-log input envelope. -/
private theorem shortLogCandidateExponent_size_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3) :
    let reduction := shortLogRecoveryTrace m ell samples
    let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples)
    Nat.size
        (shortLogCandidatePointFromCommon m ell samples reduction nearest
          offset).2.2.toNat ≤
      512 * shortLogRecoveryInputBits N m ell := by
  let reduction := shortLogRecoveryTrace m ell samples
  let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
    (shortLogLatticeTarget m ell samples)
  let point := shortLogCandidatePointFromCommon m ell samples reduction
    nearest offset
  have hcoordinate :
      point.2.2.natAbs ≤ shortLogCandidatePointMagnitude m ell samples := by
    simpa [point, reduction, nearest] using
      (shortLogCandidatePointFromCommon_coordinates_le m ell samples hoffset).2.2
  have htoNat : point.2.2.toNat ≤ point.2.2.natAbs := by
    cases point.2.2 <;> simp
  calc
    Nat.size point.2.2.toNat ≤ Nat.size point.2.2.natAbs :=
      Nat.size_le_size htoNat
    _ ≤ Nat.size (shortLogCandidatePointMagnitude m ell samples) :=
      Nat.size_le_size hcoordinate
    _ ≤ 512 * shortLogRecoveryInputBits N m ell :=
      shortLogCandidatePointMagnitude_size_le N m ell samples

/-- Every operand emitted while forming one canonical candidate lattice point
fits the same point-magnitude bit envelope. -/
private theorem shortLogPointAtOffsetExecution_maxOperandWidth_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3) :
    let reduction := shortLogRecoveryTrace m ell samples
    let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples)
    NumberTheory.arithmeticEventListMaxOperandWidth
        (shortLogPointAtOffsetExecution reduction.output nearest.center
          offset).arithmetic ≤
      512 * shortLogRecoveryInputBits N m ell := by
  let reduction := shortLogRecoveryTrace m ell samples
  let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
    (shortLogLatticeTarget m ell samples)
  let basisBound := shortLogReducedBasisBound m ell samples
  let centerBound := shortLogNearestPlaneOperandMagnitude m ell samples
  let pointBound := shortLogCandidatePointMagnitude m ell samples
  have hbasis : reduction.output.SquaredNormsLe basisBound := by
    simpa [reduction, basisBound, shortLogReducedBasisBound,
      shortLogRecoveryTrace] using
      (NumberTheory.lllReduce3WithFuel_output_squaredNormsLe
        (shortLogRecoveryFuel m ell) (shortLogLatticeBasis m ell samples)
        (shortLogLatticeBasis_fullRank m ell samples))
  have hfull : reduction.output.FullRank := by
    simpa [reduction] using shortLogRecoveryTrace_fullRank m ell samples
  have htarget : NumberTheory.integerPointSquaredNorm
      (shortLogLatticeTarget m ell samples) ≤
        2 * shortLogLatticeModulus m ell ^ 2 :=
    shortLogLatticeTarget_squaredNorm_le m ell samples
  have hcenter : nearest.center.1.natAbs ≤ centerBound ∧
      nearest.center.2.1.natAbs ≤ centerBound ∧
      nearest.center.2.2.natAbs ≤ centerBound := by
    simpa [nearest, reduction, centerBound,
      shortLogNearestPlaneOperandMagnitude, basisBound,
      shortLogReducedBasisBound] using
      (NumberTheory.nearestPlaneTrace3_center_coordinates_le
        reduction.output (shortLogLatticeTarget m ell samples)
        basisBound (2 * shortLogLatticeModulus m ell ^ 2)
        hfull hbasis htarget)
  have hoffsetBound := shortLogCoefficientOffset_coordinates_le hoffset
  have row_coordinates_le (point : NumberTheory.IntegerPoint3)
      (hpoint : NumberTheory.integerPointSquaredNorm point ≤ basisBound) :
      point.1.natAbs ≤ basisBound ∧ point.2.1.natAbs ≤ basisBound ∧
        point.2.2.natAbs ≤ basisBound := by
    have hfirst : point.1.natAbs ^ 2 ≤ basisBound := by
      exact (show point.1.natAbs ^ 2 ≤
          NumberTheory.integerPointSquaredNorm point by
        simp only [NumberTheory.integerPointSquaredNorm]
        omega).trans hpoint
    have hsecond : point.2.1.natAbs ^ 2 ≤ basisBound := by
      exact (show point.2.1.natAbs ^ 2 ≤
          NumberTheory.integerPointSquaredNorm point by
        simp only [NumberTheory.integerPointSquaredNorm]
        omega).trans hpoint
    have hthird : point.2.2.natAbs ^ 2 ≤ basisBound := by
      exact (show point.2.2.natAbs ^ 2 ≤
          NumberTheory.integerPointSquaredNorm point by
        simp only [NumberTheory.integerPointSquaredNorm]
        omega).trans hpoint
    exact
      ⟨(Nat.le_self_pow (by decide) _).trans hfirst,
        (Nat.le_self_pow (by decide) _).trans hsecond,
        (Nat.le_self_pow (by decide) _).trans hthird⟩
  have hfirst := row_coordinates_le reduction.output.first hbasis.1
  have hsecond := row_coordinates_le reduction.output.second hbasis.2.1
  have hthird := row_coordinates_le reduction.output.third hbasis.2.2
  have hcoefficients :
      (nearest.center.1 + offset.1).natAbs ≤ centerBound + 42 ∧
        (nearest.center.2.1 + offset.2.1).natAbs ≤ centerBound + 42 ∧
        (nearest.center.2.2 + offset.2.2).natAbs ≤ centerBound + 42 :=
    ⟨(Int.natAbs_add_le _ _).trans
        (Nat.add_le_add hcenter.1 hoffsetBound.1),
      (Int.natAbs_add_le _ _).trans
        ((Nat.add_le_add hcenter.2.1 hoffsetBound.2.1).trans (by omega)),
      (Int.natAbs_add_le _ _).trans
        ((Nat.add_le_add hcenter.2.2 hoffsetBound.2.2).trans (by omega))⟩
  have hpointFormula : pointBound =
      3 * (centerBound + 43) * (basisBound + 1) := by
    rfl
  have hpointSize : Nat.size pointBound ≤
      512 * shortLogRecoveryInputBits N m ell := by
    simpa [pointBound] using
      shortLogCandidatePointMagnitude_size_le N m ell samples
  have hbasic : centerBound ≤ pointBound ∧ 42 ≤ pointBound ∧
      centerBound + 42 ≤ pointBound ∧ basisBound ≤ pointBound := by
    rw [hpointFormula]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  have h34 : 34 ≤ pointBound := by omega
  let productBound := (centerBound + 42) * basisBound
  have htripleProduct : 3 * productBound ≤ pointBound := by
    simp only [productBound]
    rw [hpointFormula]
    nlinarith
  have hproductToPoint : productBound ≤ pointBound := by omega
  have hdoubleProductToPoint : 2 * productBound ≤ pointBound := by omega
  have hmul {coefficient coordinate : Int}
      (hcoefficient : coefficient.natAbs ≤ centerBound + 42)
      (hcoordinate : coordinate.natAbs ≤ basisBound) :
      (coefficient * coordinate).natAbs ≤ productBound := by
    simp only [Int.natAbs_mul, productBound]
    exact Nat.mul_le_mul hcoefficient hcoordinate
  have haddProducts {left right : Int}
      (hleft : left.natAbs ≤ productBound)
      (hright : right.natAbs ≤ productBound) :
      (left + right).natAbs ≤ 2 * productBound := by
    exact (Int.natAbs_add_le _ _).trans (by omega)
  have hwidth {left right : Int}
      (hleft : left.natAbs ≤ pointBound)
      (hright : right.natAbs ≤ pointBound) :
      max (NumberTheory.integerMagnitudeBits left)
          (NumberTheory.integerMagnitudeBits right) ≤ Nat.size pointBound :=
    max_le (Nat.size_le_size hleft) (Nat.size_le_size hright)
  apply hpointSize.trans'
  apply NumberTheory.arithmeticEventListMaxOperandWidth_le
  intro event hevent
  simp only [shortLogPointAtOffsetExecution, shortLogPointAddExecution,
    shortLogLinearCombinationExecution, shortLogIntAddExecution,
    shortLogIntMulExecution, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hevent
  simp only [or_assoc] at hevent
  rcases hevent with (h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h)
  · subst event
    exact hwidth (hcenter.1.trans hbasic.1)
      (hoffsetBound.1.trans hbasic.2.1)
  · subst event
    exact hwidth (hcenter.2.1.trans hbasic.1)
      (hoffsetBound.2.1.trans h34)
  · subst event
    exact hwidth (hcenter.2.2.trans hbasic.1)
      (hoffsetBound.2.2.trans h34)
  · subst event
    exact hwidth (hcoefficients.1.trans hbasic.2.2.1)
      (hfirst.1.trans hbasic.2.2.2)
  · subst event
    exact hwidth (hcoefficients.1.trans hbasic.2.2.1)
      (hfirst.2.1.trans hbasic.2.2.2)
  · subst event
    exact hwidth (hcoefficients.1.trans hbasic.2.2.1)
      (hfirst.2.2.trans hbasic.2.2.2)
  · subst event
    exact hwidth (hcoefficients.2.1.trans hbasic.2.2.1)
      (hsecond.1.trans hbasic.2.2.2)
  · subst event
    exact hwidth (hcoefficients.2.1.trans hbasic.2.2.1)
      (hsecond.2.1.trans hbasic.2.2.2)
  · subst event
    exact hwidth (hcoefficients.2.1.trans hbasic.2.2.1)
      (hsecond.2.2.trans hbasic.2.2.2)
  · subst event
    exact hwidth (hcoefficients.2.2.trans hbasic.2.2.1)
      (hthird.1.trans hbasic.2.2.2)
  · subst event
    exact hwidth (hcoefficients.2.2.trans hbasic.2.2.1)
      (hthird.2.1.trans hbasic.2.2.2)
  · subst event
    exact hwidth (hcoefficients.2.2.trans hbasic.2.2.1)
      (hthird.2.2.trans hbasic.2.2.2)
  · subst event
    exact hwidth
      ((hmul hcoefficients.2.1 hsecond.1).trans hproductToPoint)
      ((hmul hcoefficients.2.2 hthird.1).trans hproductToPoint)
  · subst event
    exact hwidth
      ((hmul hcoefficients.2.1 hsecond.2.1).trans hproductToPoint)
      ((hmul hcoefficients.2.2 hthird.2.1).trans hproductToPoint)
  · subst event
    exact hwidth
      ((hmul hcoefficients.2.1 hsecond.2.2).trans hproductToPoint)
      ((hmul hcoefficients.2.2 hthird.2.2).trans hproductToPoint)
  · subst event
    exact hwidth
      ((hmul hcoefficients.1 hfirst.1).trans hproductToPoint)
      ((haddProducts
          (hmul hcoefficients.2.1 hsecond.1)
          (hmul hcoefficients.2.2 hthird.1)).trans
        hdoubleProductToPoint)
  · subst event
    exact hwidth
      ((hmul hcoefficients.1 hfirst.2.1).trans hproductToPoint)
      ((haddProducts
          (hmul hcoefficients.2.1 hsecond.2.1)
          (hmul hcoefficients.2.2 hthird.2.1)).trans
        hdoubleProductToPoint)
  · subst event
    exact hwidth
      ((hmul hcoefficients.1 hfirst.2.2).trans hproductToPoint)
      ((haddProducts
          (hmul hcoefficients.2.1 hsecond.2.2)
          (hmul hcoefficients.2.2 hthird.2.2)).trans
        hdoubleProductToPoint)

/-- Evaluate the three coordinate differences, their three squares, and both
additions in one exact squared-distance execution. -/
private def shortLogSquaredDistanceExecution
    (left right : NumberTheory.IntegerPoint3) :
    ShortLogArithmeticExecution Nat :=
  let firstDifference := shortLogIntSubExecution left.1 right.1
  let secondDifference := shortLogIntSubExecution left.2.1 right.2.1
  let thirdDifference := shortLogIntSubExecution left.2.2 right.2.2
  let firstSquare := shortLogNatMulExecution
    firstDifference.value.natAbs firstDifference.value.natAbs
  let secondSquare := shortLogNatMulExecution
    secondDifference.value.natAbs secondDifference.value.natAbs
  let thirdSquare := shortLogNatMulExecution
    thirdDifference.value.natAbs thirdDifference.value.natAbs
  let firstTwo := shortLogNatAddExecution firstSquare.value secondSquare.value
  let total := shortLogNatAddExecution firstTwo.value thirdSquare.value
  { value := total.value
    arithmetic :=
      firstDifference.arithmetic ++ secondDifference.arithmetic ++
      thirdDifference.arithmetic ++ firstSquare.arithmetic ++
      secondSquare.arithmetic ++ thirdSquare.arithmetic ++
      firstTwo.arithmetic ++ total.arithmetic }

/-- The audited distance execution computes the ordinary squared Euclidean
distance of the same two integer points. -/
private theorem shortLogSquaredDistanceExecution_value
    (left right : NumberTheory.IntegerPoint3) :
    (shortLogSquaredDistanceExecution left right).value =
      NumberTheory.squaredDistance left.toVector right.toVector := by
  rw [NumberTheory.squaredDistance_point3]
  simp [shortLogSquaredDistanceExecution, shortLogIntSubExecution,
    shortLogNatMulExecution, shortLogNatAddExecution, pow_two, Nat.add_assoc]

/-- Squared-distance arithmetic has linear operand width in the coordinate
width supplied by its two input points. -/
private theorem shortLogSquaredDistanceExecution_maxOperandWidth_le
    (left right : NumberTheory.IntegerPoint3) (width : Nat)
    (hleft :
      NumberTheory.integerMagnitudeBits left.1 ≤ width ∧
      NumberTheory.integerMagnitudeBits left.2.1 ≤ width ∧
      NumberTheory.integerMagnitudeBits left.2.2 ≤ width)
    (hright :
      NumberTheory.integerMagnitudeBits right.1 ≤ width ∧
      NumberTheory.integerMagnitudeBits right.2.1 ≤ width ∧
      NumberTheory.integerMagnitudeBits right.2.2 ≤ width) :
    NumberTheory.arithmeticEventListMaxOperandWidth
        (shortLogSquaredDistanceExecution left right).arithmetic ≤
      2 * width + 3 := by
  have difference_size (a b : Int)
      (ha : NumberTheory.integerMagnitudeBits a ≤ width)
      (hb : NumberTheory.integerMagnitudeBits b ≤ width) :
      Nat.size (a - b).natAbs ≤ width + 1 := by
    calc
      Nat.size (a - b).natAbs ≤ Nat.size (a.natAbs + b.natAbs) :=
        Nat.size_le_size (Int.natAbs_sub_le a b)
      _ ≤ max (Nat.size a.natAbs) (Nat.size b.natAbs) + 1 :=
        NumberTheory.natSize_add_le_max_add_one _ _
      _ ≤ width + 1 := Nat.add_le_add_right (max_le ha hb) 1
  let firstDifference := (left.1 - right.1).natAbs
  let secondDifference := (left.2.1 - right.2.1).natAbs
  let thirdDifference := (left.2.2 - right.2.2).natAbs
  have hfirst : Nat.size firstDifference ≤ width + 1 :=
    difference_size left.1 right.1 hleft.1 hright.1
  have hsecond : Nat.size secondDifference ≤ width + 1 :=
    difference_size left.2.1 right.2.1 hleft.2.1 hright.2.1
  have hthird : Nat.size thirdDifference ≤ width + 1 :=
    difference_size left.2.2 right.2.2 hleft.2.2 hright.2.2
  have square_size (value : Nat) (hvalue : Nat.size value ≤ width + 1) :
      Nat.size (value * value) ≤ 2 * width + 2 := by
    calc
      Nat.size (value * value) ≤ Nat.size value + Nat.size value :=
        NumberTheory.natSize_mul_le_add _ _
      _ ≤ 2 * width + 2 := by omega
  have hfirstSquare := square_size firstDifference hfirst
  have hsecondSquare := square_size secondDifference hsecond
  have hthirdSquare := square_size thirdDifference hthird
  have hfirstTwo :
      Nat.size (firstDifference * firstDifference +
        secondDifference * secondDifference) ≤ 2 * width + 3 := by
    calc
      _ ≤ max (Nat.size (firstDifference * firstDifference))
          (Nat.size (secondDifference * secondDifference)) + 1 :=
        NumberTheory.natSize_add_le_max_add_one _ _
      _ ≤ 2 * width + 3 := by omega
  apply NumberTheory.arithmeticEventListMaxOperandWidth_le
  intro event hevent
  simp only [shortLogSquaredDistanceExecution, shortLogIntSubExecution,
    shortLogNatMulExecution, shortLogNatAddExecution, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hevent
  simp only [or_assoc] at hevent
  rcases hevent with h | h | h | h | h | h | h | h
  · subst event
    exact (max_le hleft.1 hright.1).trans (by omega)
  · subst event
    exact (max_le hleft.2.1 hright.2.1).trans (by omega)
  · subst event
    exact (max_le hleft.2.2 hright.2.2).trans (by omega)
  · subst event
    exact (max_le hfirst hfirst).trans (by omega)
  · subst event
    exact (max_le hsecond hsecond).trans (by omega)
  · subst event
    exact (max_le hthird hthird).trans (by omega)
  · subst event
    exact (max_le hfirstSquare hsecondSquare).trans (by omega)
  · subst event
    exact
      (max_le hfirstTwo (by
        simpa [thirdDifference] using hthirdSquare.trans (by omega))).trans
          (by omega)

/-- The value emitted by squared-distance arithmetic has at most twice the
coordinate width, up to a fixed carry allowance. -/
private theorem shortLogSquaredDistanceExecution_value_size_le
    (left right : NumberTheory.IntegerPoint3) (width : Nat)
    (hleft :
      NumberTheory.integerMagnitudeBits left.1 ≤ width ∧
      NumberTheory.integerMagnitudeBits left.2.1 ≤ width ∧
      NumberTheory.integerMagnitudeBits left.2.2 ≤ width)
    (hright :
      NumberTheory.integerMagnitudeBits right.1 ≤ width ∧
      NumberTheory.integerMagnitudeBits right.2.1 ≤ width ∧
      NumberTheory.integerMagnitudeBits right.2.2 ≤ width) :
    Nat.size (shortLogSquaredDistanceExecution left right).value ≤
      2 * width + 4 := by
  have difference_size (a b : Int)
      (ha : NumberTheory.integerMagnitudeBits a ≤ width)
      (hb : NumberTheory.integerMagnitudeBits b ≤ width) :
      Nat.size (a - b).natAbs ≤ width + 1 := by
    calc
      Nat.size (a - b).natAbs ≤ Nat.size (a.natAbs + b.natAbs) :=
        Nat.size_le_size (Int.natAbs_sub_le a b)
      _ ≤ max (Nat.size a.natAbs) (Nat.size b.natAbs) + 1 :=
        NumberTheory.natSize_add_le_max_add_one _ _
      _ ≤ width + 1 := Nat.add_le_add_right (max_le ha hb) 1
  have square_size (value : Nat) (hvalue : Nat.size value ≤ width + 1) :
      Nat.size (value * value) ≤ 2 * width + 2 := by
    exact (NumberTheory.natSize_mul_le_add value value).trans (by omega)
  let firstDifference := (left.1 - right.1).natAbs
  let secondDifference := (left.2.1 - right.2.1).natAbs
  let thirdDifference := (left.2.2 - right.2.2).natAbs
  have hfirstSquare :
      Nat.size (firstDifference * firstDifference) ≤ 2 * width + 2 :=
    square_size firstDifference
      (difference_size left.1 right.1 hleft.1 hright.1)
  have hsecondSquare :
      Nat.size (secondDifference * secondDifference) ≤ 2 * width + 2 :=
    square_size secondDifference
      (difference_size left.2.1 right.2.1 hleft.2.1 hright.2.1)
  have hthirdSquare :
      Nat.size (thirdDifference * thirdDifference) ≤ 2 * width + 2 :=
    square_size thirdDifference
      (difference_size left.2.2 right.2.2 hleft.2.2 hright.2.2)
  have hfirstTwo :
      Nat.size (firstDifference * firstDifference +
        secondDifference * secondDifference) ≤ 2 * width + 3 := by
    exact
      (NumberTheory.natSize_add_le_max_add_one _ _).trans (by omega)
  simp only [firstDifference, secondDifference] at hfirstTwo
  simp only [thirdDifference] at hthirdSquare
  simp only [shortLogSquaredDistanceExecution, shortLogIntSubExecution,
    shortLogNatMulExecution, shortLogNatAddExecution]
  exact (NumberTheory.natSize_add_le_max_add_one _ _).trans (by omega)

/-- Center of the quadratic whose roots are the two RSA factors. -/
def quadraticCenter (shortLog : Nat) : Nat :=
  shortLog + 1

/-- Discriminant of the factor-recovery quadratic. -/
def quadraticDiscriminant (N shortLog : Nat) : Nat :=
  quadraticCenter shortLog ^ 2 - N

/-- One sealed quadratic factor-recovery execution.  Both candidate divisors
are checked unconditionally before the first valid one is selected. -/
structure QuadraticFactorRecoveryTrace where
  private mk ::
  /-- Exact arithmetic emitted by the quadratic and both divisor checks. -/
  arithmetic : List NumberTheory.ArithmeticEvent
  /-- Candidate roots, absent only when no short logarithm was recovered. -/
  candidates : Option (Nat × Nat)
  /-- First nontrivial divisor among the two fully checked candidates. -/
  result : Option Nat

/-- Exact schoolbook charge of the quadratic execution. -/
def QuadraticFactorRecoveryTrace.schoolbookCharge
    (trace : QuadraticFactorRecoveryTrace) : Nat :=
  NumberTheory.arithmeticEventListCharge trace.arithmetic

/-- Execute the quadratic recovery from an optional short logarithm.  The
integer square root is the value of the sealed Newton trace, never a detached
native computation. -/
def quadraticFactorRecoveryTrace (N : Nat) (shortLog : Option Nat) :
    QuadraticFactorRecoveryTrace :=
  match shortLog with
  | none => .mk [] none none
  | some shortLog =>
      let center := shortLog + 1
      let centerSquare := center * center
      let discriminant := centerSquare - N
      let rootTrace := NumberTheory.integerSquareRootTrace discriminant
      let firstCandidate := center - rootTrace.value
      let secondCandidate := center + rootTrace.value
      let firstRemainder := N % firstCandidate
      let secondRemainder := N % secondCandidate
      let firstDivides := firstRemainder = 0
      let secondDivides := secondRemainder = 0
      let firstValid := 1 < firstCandidate ∧ firstCandidate < N ∧ firstDivides
      let secondValid :=
        1 < secondCandidate ∧ secondCandidate < N ∧ secondDivides
      let result :=
        if firstValid then some firstCandidate
        else if secondValid then some secondCandidate
        else none
      .mk
        ([ .natAdd shortLog 1
         , .natMul center center
         , .natSub centerSquare N ] ++
          rootTrace.arithmetic ++
          [ .natSub center rootTrace.value
          , .natAdd center rootTrace.value
          , .natLt 1 firstCandidate
          , .natLt firstCandidate N
          , .natMod N firstCandidate
          , .natEq firstRemainder 0
          , .natLt 1 secondCandidate
          , .natLt secondCandidate N
          , .natMod N secondCandidate
          , .natEq secondRemainder 0 ])
        (some (firstCandidate, secondCandidate)) result

/-- A quadratic trace indexed by the exact selector output that produced it.
The stored equality prevents an opaque caller from pairing unrelated factor
work with a short-log result. -/
structure QuadraticFactorRecoveryExecution (N : Nat)
    (shortLog : Option Nat) where
  private mk ::
  /-- Canonical closed quadratic execution. -/
  trace : QuadraticFactorRecoveryTrace
  /-- The stored execution is exactly the one computed from this input. -/
  canonical : trace = quadraticFactorRecoveryTrace N shortLog

-- Constructor injectivity expands the proof field into a redundant equality.
-- Keep the exception scoped to the generated declaration.
attribute [-simp] QuadraticFactorRecoveryExecution.mk.injEq
attribute [nolint simpNF] QuadraticFactorRecoveryExecution.mk.injEq

/-- Build the uniquely certified quadratic execution for one selector output. -/
def quadraticFactorRecoveryExecution (N : Nat) (shortLog : Option Nat) :
    QuadraticFactorRecoveryExecution N shortLog :=
  .mk (quadraticFactorRecoveryTrace N shortLog) rfl

/-- Candidate factors are a projection of the unique quadratic execution. -/
def quadraticFactorCandidates (N shortLog : Nat) : Nat × Nat :=
  (quadraticFactorRecoveryTrace N (some shortLog)).candidates.getD (0, 0)

/-- The candidate projection of the sealed quadratic execution is the usual
pair formed from the exact integer square root of the discriminant. -/
theorem quadraticFactorCandidates_eq (N shortLog : Nat) :
    quadraticFactorCandidates N shortLog =
      (quadraticCenter shortLog - Nat.sqrt (quadraticDiscriminant N shortLog),
        quadraticCenter shortLog + Nat.sqrt (quadraticDiscriminant N shortLog)) := by
  simp only [quadraticFactorCandidates, quadraticFactorRecoveryTrace]
  rw [NumberTheory.integerSquareRootTrace_value]
  simp [quadraticCenter, quadraticDiscriminant, pow_two]

/-- Factor selection is a projection of the same quadratic execution that
supplies its exact arithmetic. -/
def recoverFactorFromShortLog (N shortLog : Nat) : Option Nat :=
  (quadraticFactorRecoveryTrace N (some shortLog)).result

/-- The result projection of the sealed quadratic execution performs the two
range and divisibility checks in the recorded order. -/
theorem recoverFactorFromShortLog_eq (N shortLog : Nat) :
    recoverFactorFromShortLog N shortLog =
      let firstCandidate := quadraticCenter shortLog -
        Nat.sqrt (quadraticDiscriminant N shortLog)
      let secondCandidate := quadraticCenter shortLog +
        Nat.sqrt (quadraticDiscriminant N shortLog)
      if 1 < firstCandidate ∧ firstCandidate < N ∧
          N % firstCandidate = 0 then
        some firstCandidate
      else if 1 < secondCandidate ∧ secondCandidate < N ∧
          N % secondCandidate = 0 then
        some secondCandidate
      else
        none := by
  simp only [recoverFactorFromShortLog, quadraticFactorRecoveryTrace]
  rw [NumberTheory.integerSquareRootTrace_value]
  simp [quadraticCenter, quadraticDiscriminant, pow_two]

end SealedPairArithmetic

/-- Preserve the first successful candidate while a left fold continues to
visit every remaining validation slot. -/
def retainFirstShortLogCandidate (selected checked : Option Nat) : Option Nat :=
  match selected with
  | some candidate => some candidate
  | none => checked

section SealedPairRecoveryTrace

/-- One offset validation result and every arithmetic event emitted by the
same closed execution. -/
structure ShortLogCandidateCheckTrace (N : Nat) where
  private mk ::
  /-- Canonical coefficient offset for this scan slot. -/
  offset : NumberTheory.IntegerPoint3
  /-- Actual lattice point computed from the shared nearest center. -/
  point : ShortLogLatticePoint
  /-- Candidate group power computed by the sealed fixed-width scan. -/
  candidatePower : NumberTheory.ModularPowerTrace N
  /-- Operand-derived point, predicate, and modular-power arithmetic. -/
  arithmetic : List NumberTheory.ArithmeticEvent
  /-- Candidate value exactly when all closed checks pass. -/
  result : Option Nat

/-- Exact pre-state accumulator tag inspected by the first-success fold. -/
private def shortLogSelectorTag (selected : Option Nat) :
    NumberTheory.ArithmeticEvent :=
  .natEq (if selected.isSome then 1 else 0) 1

/-- Arithmetic consumed by one slot when it is visited by the full selector,
including the actual pre-state accumulator check after the candidate work. -/
def ShortLogCandidateCheckTrace.selectorArithmeticFrom {N : Nat}
    (trace : ShortLogCandidateCheckTrace N) (selected : Option Nat) :
    List NumberTheory.ArithmeticEvent :=
  trace.arithmetic ++ [shortLogSelectorTag selected]

/-- Internal values produced by one candidate slot before its final closed
predicate is evaluated.  Keeping these operands separate from the event list
lets proofs reason about the value path without unfolding millions of list
cells or the arithmetic concatenation. -/
private structure ShortLogCandidateExecution (N : Nat) where
  point : ShortLogLatticePoint
  distance : Nat
  scaledDistance : Nat
  rangeBound : Nat
  scaledRange : Nat
  candidatePower : NumberTheory.ModularPowerTrace N
  arithmetic : List NumberTheory.ArithmeticEvent

/-- Execute all operand-producing work for one candidate slot. -/
@[noinline]
private def shortLogCandidateExecutionFromCommon {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (reduction : NumberTheory.LatticeReductionTrace3)
    (nearest : NumberTheory.NearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples))
    (offset : NumberTheory.IntegerPoint3) : ShortLogCandidateExecution N :=
  let target := shortLogLatticeTarget m ell samples
  let pointExecution := shortLogPointAtOffsetExecution
    reduction.output nearest.center offset
  let point := pointExecution.value
  let distance := shortLogSquaredDistanceExecution point target
  let scaledDistance := shortLogNatMulExecution 8 distance.value
  let rangeBound := 1 <<< m
  let rangeSquare := shortLogNatMulExecution rangeBound rangeBound
  let scaledRange := shortLogNatMulExecution 9 rangeSquare.value
  let rangeSuccessor := shortLogIntAddExecution point.2.2 1
  let candidate := point.2.2.toNat
  let candidatePower := NumberTheory.modularPowerTrace (Nat.size candidate)
    generator.val candidate
  { point := point
    distance := distance.value
    scaledDistance := scaledDistance.value
    rangeBound := rangeBound
    scaledRange := scaledRange.value
    candidatePower := candidatePower
    arithmetic :=
      pointExecution.arithmetic ++ distance.arithmetic ++
        scaledDistance.arithmetic ++ [.natShiftLeft 1 m] ++
        rangeSquare.arithmetic ++ scaledRange.arithmetic ++
        [ .natLt scaledDistance.value scaledRange.value
        , .intLe 1 point.2.2 ] ++ rangeSuccessor.arithmetic ++
        [ .intLe rangeSuccessor.value (rangeBound : Int) ] ++
        [ .natLog2 candidate ] ++
        candidatePower.arithmetic }

/-- Final result predicate over the values emitted by one slot execution and
the target power shared by the pair. -/
private def shortLogCandidateExecutionResult {N : Nat}
    (execution : ShortLogCandidateExecution N)
    (targetPower : NumberTheory.ModularPowerTrace N) : Option Nat :=
  let candidate := execution.point.2.2.toNat
  if execution.scaledDistance < execution.scaledRange ∧
      0 < execution.point.2.2 ∧
      execution.point.2.2 < (execution.rangeBound : Nat) ∧
      execution.candidatePower.value = targetPower.value then
    some candidate
  else
    none

/-- Execute one candidate slot from the shared reduction, nearest center, and
target power.  The candidate power is always evaluated by the sealed fixed-
width modular-power trace. -/
def shortLogCandidateCheckTraceFromCommon {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (reduction : NumberTheory.LatticeReductionTrace3)
    (nearest : NumberTheory.NearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples))
    (targetPower : NumberTheory.ModularPowerTrace N)
    (offset : NumberTheory.IntegerPoint3) :
    ShortLogCandidateCheckTrace N :=
  let execution := shortLogCandidateExecutionFromCommon m ell generator
    samples reduction nearest offset
  let result := shortLogCandidateExecutionResult execution targetPower
  .mk offset execution.point execution.candidatePower
    (execution.arithmetic ++
      [ .natEq execution.candidatePower.value.val targetPower.value.val ])
    result

/-- Both centered target coordinates fit in the public recovery input
envelope; the third target coordinate is zero. -/
private theorem shortLogLatticeTarget_coordinate_width_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    let target := shortLogLatticeTarget m ell samples
    NumberTheory.integerMagnitudeBits target.1 ≤
        shortLogRecoveryInputBits N m ell ∧
      NumberTheory.integerMagnitudeBits target.2.1 ≤
        shortLogRecoveryInputBits N m ell ∧
      NumberTheory.integerMagnitudeBits target.2.2 ≤
        shortLogRecoveryInputBits N m ell := by
  have hmodulus : 0 < shortLogLatticeModulus m ell := by
    simp [shortLogLatticeModulus]
  have coordinate_width (sample : ShortLogSample m ell) :
      NumberTheory.integerMagnitudeBits
          (shortLogTargetCoordinate m ell sample) ≤
        shortLogRecoveryInputBits N m ell := by
    have habs :
        (shortLogTargetCoordinate m ell sample).natAbs ≤
          shortLogLatticeModulus m ell := by
      have htwice :
          2 * (shortLogTargetCoordinate m ell sample).natAbs ≤
            shortLogLatticeModulus m ell := by
        simpa [shortLogTargetCoordinate] using
          (NumberTheory.two_mul_natAbs_centeredResidue_le
            (value := NumberTheory.modularNegation
              (shortLogLatticeModulus m ell) (2 ^ m * sample.2.val))
            hmodulus)
      omega
    calc
      NumberTheory.integerMagnitudeBits
          (shortLogTargetCoordinate m ell sample) ≤
          Nat.size (shortLogLatticeModulus m ell) := Nat.size_le_size habs
      _ = ell + m + 1 := by
        rw [shortLogLatticeModulus, Nat.size_pow]
      _ ≤ shortLogRecoveryInputBits N m ell := by
        simp only [shortLogRecoveryInputBits]
        omega
  exact
    ⟨coordinate_width samples.1, coordinate_width samples.2, by
      simp [shortLogLatticeTarget, NumberTheory.integerMagnitudeBits,
        shortLogRecoveryInputBits]⟩

/-- One canonical candidate slot emits 37 fixed arithmetic events plus seven
modular-power events for every bit of the actual candidate exponent. -/
private theorem
    shortLogCandidateCheckTraceFromCommon_selectorArithmeticFrom_length
    {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (reduction : NumberTheory.LatticeReductionTrace3)
    (nearest : NumberTheory.NearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples))
    (targetPower : NumberTheory.ModularPowerTrace N)
    (offset : NumberTheory.IntegerPoint3) (selected : Option Nat) :
    ((shortLogCandidateCheckTraceFromCommon m ell generator samples reduction
      nearest targetPower offset).selectorArithmeticFrom selected).length =
        37 + 7 * Nat.size
          (shortLogCandidatePointFromCommon m ell samples reduction
            nearest offset).2.2.toNat := by
  simp only [shortLogCandidateCheckTraceFromCommon,
    ShortLogCandidateCheckTrace.selectorArithmeticFrom, shortLogSelectorTag,
    shortLogCandidateExecutionFromCommon,
    shortLogCandidatePointFromCommon,
    shortLogPointAtOffsetExecution, shortLogPointAddExecution,
    shortLogLinearCombinationExecution,
    shortLogSquaredDistanceExecution,
    shortLogIntAddExecution, shortLogIntSubExecution,
    shortLogIntMulExecution, shortLogNatAddExecution,
    shortLogNatMulExecution, List.length_append, List.length_cons,
    List.length_nil, NumberTheory.modularPowerTrace_arithmetic_length]
  ring

/-- Every event in one canonical validation slot has operand width linear in
the public short-log input envelope.  The deliberately loose coefficient keeps
the proof independent of concrete RSA key sizes. -/
private theorem
    shortLogCandidateCheckTraceFromCommon_selectorArithmeticFrom_maxOperandWidth_le
    {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3)
    (selected : Option Nat)
    (hN : 0 < N) :
    let reduction := shortLogRecoveryTrace m ell samples
    let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples)
    let targetPower := NumberTheory.modularPowerTrace
      (Nat.size (targetExponent N)) generator.val (targetExponent N)
    NumberTheory.arithmeticEventListMaxOperandWidth
        ((shortLogCandidateCheckTraceFromCommon m ell generator samples
          reduction nearest targetPower offset).selectorArithmeticFrom
            selected) ≤
      2 ^ 20 * shortLogRecoveryInputBits N m ell := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let reduction := shortLogRecoveryTrace m ell samples
  let target := shortLogLatticeTarget m ell samples
  let nearest := NumberTheory.nearestPlaneTrace3 reduction.output target
  let point := shortLogCandidatePointFromCommon m ell samples reduction
    nearest offset
  let distance := shortLogSquaredDistanceExecution point target
  let rangeBound := 1 <<< m
  let targetPower := NumberTheory.modularPowerTrace
    (Nat.size (targetExponent N)) generator.val (targetExponent N)
  have hinputBitsPos : 1 ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hpointCoordinates :=
    shortLogCandidatePointFromCommon_coordinates_le m ell samples hoffset
  have hpointMagnitudeSize :=
    shortLogCandidatePointMagnitude_size_le N m ell samples
  have hpointWidth :
      NumberTheory.integerMagnitudeBits point.1 ≤ 512 * inputBits ∧
      NumberTheory.integerMagnitudeBits point.2.1 ≤ 512 * inputBits ∧
      NumberTheory.integerMagnitudeBits point.2.2 ≤ 512 * inputBits := by
    simpa [point, reduction, nearest, inputBits] using
      ⟨(Nat.size_le_size hpointCoordinates.1).trans hpointMagnitudeSize,
        (Nat.size_le_size hpointCoordinates.2.1).trans hpointMagnitudeSize,
        (Nat.size_le_size hpointCoordinates.2.2).trans hpointMagnitudeSize⟩
  have htargetWidth :
      NumberTheory.integerMagnitudeBits target.1 ≤ 512 * inputBits ∧
      NumberTheory.integerMagnitudeBits target.2.1 ≤ 512 * inputBits ∧
      NumberTheory.integerMagnitudeBits target.2.2 ≤ 512 * inputBits := by
    have h := shortLogLatticeTarget_coordinate_width_le
      N m ell samples
    simpa [target, inputBits] using
      ⟨h.1.trans (by omega), h.2.1.trans (by omega),
        h.2.2.trans (by omega)⟩
  have hpointArithmetic :
      NumberTheory.arithmeticEventListMaxOperandWidth
          (shortLogPointAtOffsetExecution reduction.output nearest.center
            offset).arithmetic ≤ 512 * inputBits := by
    simpa [reduction, nearest, inputBits] using
      shortLogPointAtOffsetExecution_maxOperandWidth_le
        N m ell samples hoffset
  have hdistanceArithmetic :
      NumberTheory.arithmeticEventListMaxOperandWidth distance.arithmetic ≤
        1024 * inputBits + 3 := by
    have h :=
      shortLogSquaredDistanceExecution_maxOperandWidth_le point target
        (512 * inputBits) hpointWidth htargetWidth
    simp only [distance] at h ⊢
    omega
  have hdistanceValue :
      Nat.size distance.value ≤ 1024 * inputBits + 4 := by
    have h :=
      shortLogSquaredDistanceExecution_value_size_le point target
        (512 * inputBits) hpointWidth htargetWidth
    simp only [distance] at h ⊢
    omega
  have hrangeBoundSize : Nat.size rangeBound ≤ inputBits := by
    have hm : m + 1 ≤ inputBits := by
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega
    change Nat.size (1 <<< m) ≤ inputBits
    rw [Nat.one_shiftLeft, Nat.size_pow]
    exact hm
  have hrangeSquareSize :
      Nat.size (rangeBound * rangeBound) ≤ 2 * inputBits := by
    exact (NumberTheory.natSize_mul_le_add _ _).trans (by omega)
  have hscaledDistanceSize :
      Nat.size (8 * distance.value) ≤ 1024 * inputBits + 8 := by
    have hsizeEight : Nat.size 8 = 4 := by decide
    calc
      _ ≤ Nat.size 8 + Nat.size distance.value :=
        NumberTheory.natSize_mul_le_add _ _
      _ ≤ 1024 * inputBits + 8 := by omega
  have hscaledRangeSize :
      Nat.size (9 * (rangeBound * rangeBound)) ≤ 2 * inputBits + 4 := by
    have hsizeNine : Nat.size 9 = 4 := by decide
    calc
      _ ≤ Nat.size 9 + Nat.size (rangeBound * rangeBound) :=
        NumberTheory.natSize_mul_le_add _ _
      _ ≤ 2 * inputBits + 4 := by omega
  have hrangeSuccessorSize :
      NumberTheory.integerMagnitudeBits (point.2.2 + 1) ≤
        512 * inputBits + 1 := by
    calc
      Nat.size (point.2.2 + 1).natAbs ≤
          Nat.size (point.2.2.natAbs + 1) :=
        Nat.size_le_size (Int.natAbs_add_le _ _)
      _ ≤ max (Nat.size point.2.2.natAbs) (Nat.size 1) + 1 :=
        NumberTheory.natSize_add_le_max_add_one _ _
      _ ≤ 512 * inputBits + 1 := by
        have hone : Nat.size 1 ≤ 512 * inputBits := by
          simp
          omega
        exact Nat.add_le_add_right (max_le hpointWidth.2.2 hone) 1
  have hcandidateSize :
      Nat.size point.2.2.toNat ≤ 512 * inputBits := by
    simpa [point, reduction, nearest, inputBits] using
      shortLogCandidateExponent_size_le N m ell samples hoffset
  have hcandidatePowerArithmetic :
      NumberTheory.arithmeticEventListMaxOperandWidth
          (NumberTheory.modularPowerTrace (Nat.size point.2.2.toNat)
            generator.val point.2.2.toNat).arithmetic ≤
        2 * (Nat.size N + Nat.size point.2.2.toNat + 1) := by
    exact NumberTheory.modularPowerTrace_maxOperandWidth_le generator.val hN
      (Nat.lt_size_self _)
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hmodulusWidth : Nat.size N ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hcandidateValueWidth :
      Nat.size
          (NumberTheory.modularPowerTrace (Nat.size point.2.2.toNat)
            generator.val point.2.2.toNat).value.val ≤ inputBits := by
    exact
      (Nat.size_le_size
        (Nat.le_of_lt (ZMod.val_lt
          (NumberTheory.modularPowerTrace (Nat.size point.2.2.toNat)
            generator.val point.2.2.toNat).value))).trans hmodulusWidth
  have htargetValueWidth : Nat.size targetPower.value.val ≤ inputBits := by
    exact
      (Nat.size_le_size
        (Nat.le_of_lt (ZMod.val_lt targetPower.value))).trans hmodulusWidth
  have hsizeM : Nat.size m ≤ inputBits := by
    exact (Nat.size_le.2 m.lt_two_pow_self).trans (by
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega)
  have hrangeBoundIntSize :
      NumberTheory.integerMagnitudeBits (rangeBound : Int) ≤ inputBits := by
    simpa [NumberTheory.integerMagnitudeBits] using hrangeBoundSize
  apply NumberTheory.arithmeticEventListMaxOperandWidth_le
  intro event hevent
  simp only [shortLogCandidateCheckTraceFromCommon,
    ShortLogCandidateCheckTrace.selectorArithmeticFrom, shortLogSelectorTag,
    shortLogCandidateExecutionFromCommon,
    shortLogNatMulExecution, shortLogIntAddExecution,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hevent
  simp only [or_assoc] at hevent
  rcases hevent with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact
      (NumberTheory.ArithmeticEvent.operandWidth_le_listMax h).trans
        (hpointArithmetic.trans (by omega))
  · exact
      (NumberTheory.ArithmeticEvent.operandWidth_le_listMax h).trans
        (hdistanceArithmetic.trans (by omega))
  · subst event
    have hsizeEight : Nat.size 8 = 4 := by decide
    exact (max_le (by rw [hsizeEight]; omega) hdistanceValue).trans (by omega)
  · subst event
    exact (max_le hsizeM hrangeBoundSize).trans (by omega)
  · subst event
    exact (max_le hrangeBoundSize hrangeBoundSize).trans (by omega)
  · subst event
    have hsizeNine : Nat.size 9 = 4 := by decide
    apply max_le
    · rw [hsizeNine]
      omega
    · exact hrangeSquareSize.trans (by omega)
  · subst event
    exact
      (max_le hscaledDistanceSize (hscaledRangeSize.trans (by omega))).trans
        (by omega)
  · subst event
    have hone : NumberTheory.integerMagnitudeBits (1 : Int) ≤
        512 * inputBits := by
      simp [NumberTheory.integerMagnitudeBits]
      omega
    exact (max_le hone hpointWidth.2.2).trans (by omega)
  · subst event
    have hone : NumberTheory.integerMagnitudeBits (1 : Int) ≤
        512 * inputBits := by
      simp [NumberTheory.integerMagnitudeBits]
      omega
    exact (max_le hpointWidth.2.2 hone).trans (by omega)
  · subst event
    apply max_le
    · exact hrangeSuccessorSize.trans (by omega)
    · simpa [rangeBound] using hrangeBoundIntSize.trans (by omega)
  · subst event
    exact hcandidateSize.trans (by omega)
  · exact
      (NumberTheory.ArithmeticEvent.operandWidth_le_listMax h).trans
        (hcandidatePowerArithmetic.trans (by omega))
  · subst event
    exact (max_le hcandidateValueWidth htargetValueWidth).trans (by omega)
  · subst event
    unfold NumberTheory.ArithmeticEvent.operandWidth
    apply max_le
    · split
      · simp
        omega
      · simp
    · simp
      omega

/-- One canonical coefficient slot has cubic schoolbook charge in the public
input envelope. -/
private theorem
    shortLogCandidateCheckTraceFromCommon_selectorArithmeticFrom_charge_le
    {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3)
    (selected : Option Nat)
    (hN : 0 < N) :
    let reduction := shortLogRecoveryTrace m ell samples
    let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples)
    let targetPower := NumberTheory.modularPowerTrace
      (Nat.size (targetExponent N)) generator.val (targetExponent N)
    NumberTheory.arithmeticEventListCharge
        ((shortLogCandidateCheckTraceFromCommon m ell generator samples
          reduction nearest targetPower offset).selectorArithmeticFrom
            selected) ≤
      2 ^ 55 * shortLogRecoveryInputBits N m ell ^ 3 := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let reduction := shortLogRecoveryTrace m ell samples
  let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
    (shortLogLatticeTarget m ell samples)
  let targetPower := NumberTheory.modularPowerTrace
    (Nat.size (targetExponent N)) generator.val (targetExponent N)
  let events :=
    (shortLogCandidateCheckTraceFromCommon m ell generator samples reduction
      nearest targetPower offset).selectorArithmeticFrom selected
  have hinputBitsPos : 1 ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hcandidateSize :
      Nat.size
          (shortLogCandidatePointFromCommon m ell samples reduction nearest
            offset).2.2.toNat ≤
        512 * inputBits := by
    simpa [reduction, nearest, inputBits] using
      shortLogCandidateExponent_size_le N m ell samples hoffset
  have hlength : events.length ≤ 3621 * inputBits := by
    have h :=
      shortLogCandidateCheckTraceFromCommon_selectorArithmeticFrom_length
        m ell generator samples reduction nearest targetPower offset selected
    simp only [events] at h ⊢
    rw [h]
    omega
  have hwidth :
      NumberTheory.arithmeticEventListMaxOperandWidth events ≤
        2 ^ 20 * inputBits := by
    simpa [events, reduction, nearest, targetPower, inputBits] using
      shortLogCandidateCheckTraceFromCommon_selectorArithmeticFrom_maxOperandWidth_le
        m ell generator samples hoffset selected hN
  have hopen :
      2 ^ 20 * inputBits + 1 ≤ (2 ^ 20 + 1) * inputBits := by
    omega
  have hsquare :
      (2 ^ 20 * inputBits + 1) ^ 2 ≤
        ((2 ^ 20 + 1) * inputBits) ^ 2 :=
    Nat.pow_le_pow_left hopen 2
  calc
    NumberTheory.arithmeticEventListCharge events ≤
        4 * events.length *
          (NumberTheory.arithmeticEventListMaxOperandWidth events + 1) ^ 2 :=
      NumberTheory.arithmeticEventListCharge_le events
    _ ≤ 4 * (3621 * inputBits) * (2 ^ 20 * inputBits + 1) ^ 2 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 hlength)
        (Nat.pow_le_pow_left (Nat.add_le_add_right hwidth 1) 2)
    _ ≤ 4 * (3621 * inputBits) *
        ((2 ^ 20 + 1) * inputBits) ^ 2 :=
      Nat.mul_le_mul_left (4 * (3621 * inputBits)) hsquare
    _ = (4 * 3621 * (2 ^ 20 + 1) ^ 2) * inputBits ^ 3 := by ring
    _ ≤ 2 ^ 55 * inputBits ^ 3 :=
      Nat.mul_le_mul_right _ (by norm_num)

/-- Compute the exact candidate trace vector by mapping the unique slot
execution over the canonical length-indexed offset vector. -/
@[noinline]
def shortLogCandidateTraceVectorFromCommon {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (reduction : NumberTheory.LatticeReductionTrace3)
    (nearest : NumberTheory.NearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples))
    (targetPower : NumberTheory.ModularPowerTrace N) :
    List.Vector (ShortLogCandidateCheckTrace N)
      (NumberTheory.coefficientOffsetBoxWork3
        NumberTheory.nearestPlaneCoefficientBounds3) :=
  NumberTheory.mapCoefficientOffsetVector3
    NumberTheory.nearestPlaneCoefficientBounds3
      (shortLogCandidateCheckTraceFromCommon m ell generator samples
        reduction nearest targetPower)

/-- Proof-facing point projection.  It uses the same audited point execution
as the canonical candidate trace. -/
def shortLogPointAtOffsetFromReduction (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (reduction : NumberTheory.LatticeReductionTrace3)
    (offset : NumberTheory.IntegerPoint3) : ShortLogLatticePoint :=
  let target := shortLogLatticeTarget m ell samples
  let nearest := NumberTheory.nearestPlaneTrace3 reduction.output target
  shortLogCandidatePointFromCommon m ell samples reduction nearest offset

/-- Proof-facing specialization of the point projection to the unique
short-log reduction trace. -/
def shortLogPointAtOffset (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3) : ShortLogLatticePoint :=
  shortLogPointAtOffsetFromReduction m ell samples
    (shortLogRecoveryTrace m ell samples) offset

/-- The proof-facing point projection is the mathematical combination around
the ordinary nearest-plane center. -/
theorem shortLogPointAtOffset_eq (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3) :
    shortLogPointAtOffset m ell samples offset =
      (shortLogRecoveryTrace m ell samples).output.linearCombination
        (NumberTheory.IntegerPoint3.add
          ((shortLogRecoveryTrace m ell samples).output.nearestPlaneCoefficientCenter
            (shortLogLatticeTarget m ell samples)) offset) := by
  unfold shortLogPointAtOffset shortLogPointAtOffsetFromReduction
  unfold shortLogCandidatePointFromCommon
  rw [shortLogPointAtOffsetExecution_value,
    NumberTheory.nearestPlaneTrace3_center]

/-- Every coordinate of a point visited by the canonical offset scan has
binary magnitude bounded by the public short-log input ledger. -/
theorem shortLogPointAtOffset_coordinate_sizes_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3) :
    Nat.size (shortLogPointAtOffset m ell samples offset).1.natAbs ≤
        512 * shortLogRecoveryInputBits N m ell ∧
      Nat.size (shortLogPointAtOffset m ell samples offset).2.1.natAbs ≤
          512 * shortLogRecoveryInputBits N m ell ∧
        Nat.size (shortLogPointAtOffset m ell samples offset).2.2.natAbs ≤
          512 * shortLogRecoveryInputBits N m ell := by
  have coordinateBounds :=
    shortLogCandidatePointFromCommon_coordinates_le m ell samples hoffset
  have magnitudeWidth :=
    shortLogCandidatePointMagnitude_size_le N m ell samples
  have publicBounds :
      (shortLogPointAtOffset m ell samples offset).1.natAbs ≤
          shortLogCandidatePointMagnitude m ell samples ∧
        (shortLogPointAtOffset m ell samples offset).2.1.natAbs ≤
            shortLogCandidatePointMagnitude m ell samples ∧
          (shortLogPointAtOffset m ell samples offset).2.2.natAbs ≤
            shortLogCandidatePointMagnitude m ell samples := by
    simpa only [shortLogPointAtOffset, shortLogPointAtOffsetFromReduction] using
      coordinateBounds
  exact
    ⟨(Nat.size_le_size publicBounds.1).trans magnitudeWidth,
      (Nat.size_le_size publicBounds.2.1).trans magnitudeWidth,
      (Nat.size_le_size publicBounds.2.2).trans magnitudeWidth⟩

/-- Both natural operands of the exact near-target comparison fit the public
candidate-slot width ledger. -/
theorem shortLogNearTarget_operand_sizes_le
    (N m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    {offset : NumberTheory.IntegerPoint3}
    (hoffset : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3) :
    let point := shortLogPointAtOffset m ell samples offset
    let target := shortLogLatticeTarget m ell samples
    Nat.size
        (8 * NumberTheory.squaredDistance point.toVector target.toVector) ≤
        2 ^ 20 * shortLogRecoveryInputBits N m ell ∧
      Nat.size (9 * (2 ^ m) ^ 2) ≤
        2 ^ 20 * shortLogRecoveryInputBits N m ell := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let point := shortLogPointAtOffset m ell samples offset
  let target := shortLogLatticeTarget m ell samples
  have inputBitsPositive : 1 ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have pointWidths :
      NumberTheory.integerMagnitudeBits point.1 ≤ 512 * inputBits ∧
        NumberTheory.integerMagnitudeBits point.2.1 ≤ 512 * inputBits ∧
          NumberTheory.integerMagnitudeBits point.2.2 ≤ 512 * inputBits := by
    simpa only [point, inputBits, NumberTheory.integerMagnitudeBits] using
      shortLogPointAtOffset_coordinate_sizes_le N m ell samples hoffset
  have targetWidths :
      NumberTheory.integerMagnitudeBits target.1 ≤ 512 * inputBits ∧
        NumberTheory.integerMagnitudeBits target.2.1 ≤ 512 * inputBits ∧
          NumberTheory.integerMagnitudeBits target.2.2 ≤ 512 * inputBits := by
    have widths := shortLogLatticeTarget_coordinate_width_le N m ell samples
    simpa only [target, inputBits] using
      ⟨widths.1.trans (by omega), widths.2.1.trans (by omega),
        widths.2.2.trans (by omega)⟩
  have distanceSize :
      Nat.size (NumberTheory.squaredDistance point.toVector target.toVector) ≤
        1024 * inputBits + 4 := by
    have distanceBound :=
      shortLogSquaredDistanceExecution_value_size_le point target
        (512 * inputBits) pointWidths targetWidths
    rw [shortLogSquaredDistanceExecution_value] at distanceBound
    omega
  have scaledDistanceSize :
      Nat.size
          (8 * NumberTheory.squaredDistance point.toVector target.toVector) ≤
        1024 * inputBits + 8 := by
    have eightSize : Nat.size 8 = 4 := by decide
    calc
      _ ≤ Nat.size 8 +
          Nat.size (NumberTheory.squaredDistance point.toVector target.toVector) :=
        NumberTheory.natSize_mul_le_add _ _
      _ ≤ 1024 * inputBits + 8 := by rw [eightSize]; omega
  have rangeSize : Nat.size (2 ^ m) ≤ inputBits := by
    rw [Nat.size_pow]
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have rangeSquareSize : Nat.size ((2 ^ m) * (2 ^ m)) ≤ 2 * inputBits :=
    (NumberTheory.natSize_mul_le_add _ _).trans (by omega)
  have scaledRangeSize : Nat.size (9 * (2 ^ m) ^ 2) ≤
      2 * inputBits + 4 := by
    have nineSize : Nat.size 9 = 4 := by decide
    rw [pow_two]
    calc
      _ ≤ Nat.size 9 + Nat.size ((2 ^ m) * (2 ^ m)) :=
        NumberTheory.natSize_mul_le_add _ _
      _ ≤ 2 * inputBits + 4 := by rw [nineSize]; omega
  dsimp only
  exact
    ⟨scaledDistanceSize.trans (by omega),
      scaledRangeSize.trans (by omega)⟩

/-- Proof-facing result projection of the same sealed candidate execution. -/
def shortLogCandidateAtOffsetFromReduction {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (reduction : NumberTheory.LatticeReductionTrace3)
    (offset : NumberTheory.IntegerPoint3) : Option Nat :=
  let target := shortLogLatticeTarget m ell samples
  let nearest := NumberTheory.nearestPlaneTrace3 reduction.output target
  let targetPower := NumberTheory.modularPowerTrace
    (Nat.size (targetExponent N)) generator.val (targetExponent N)
  (shortLogCandidateCheckTraceFromCommon m ell generator samples reduction
    nearest targetPower offset).result

/-- Proof-facing specialization of one offset result to the unique reduction
used by pair recovery. -/
def shortLogCandidateAtOffset {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3) : Option Nat :=
  shortLogCandidateAtOffsetFromReduction m ell generator samples
    (shortLogRecoveryTrace m ell samples) offset

/-- One candidate trace accepts exactly the original mathematical validation
predicate.  This theorem is the proof-facing bridge; there is no second
executable checker. -/
theorem shortLogCandidateAtOffset_eq {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (offset : NumberTheory.IntegerPoint3) :
    shortLogCandidateAtOffset m ell generator samples offset =
      let point := shortLogPointAtOffset m ell samples offset
      if ShortLogNearTarget m ell samples point ∧
          0 < point.2.2 ∧ point.2.2 < (2 ^ m : Nat) ∧
            generator ^ point.2.2.toNat = targetUnit generator then
        some point.2.2.toNat
      else
        none := by
  simp only [shortLogCandidateAtOffset,
    shortLogCandidateAtOffsetFromReduction,
    shortLogCandidateCheckTraceFromCommon]
  unfold shortLogCandidateExecutionResult
  simp only [shortLogCandidateExecutionFromCommon,
    shortLogNatMulExecution, shortLogSquaredDistanceExecution_value,
    Nat.one_shiftLeft]
  rw [NumberTheory.modularPowerTrace_value generator.val
      (Nat.lt_size_self _),
    NumberTheory.modularPowerTrace_value generator.val
      (Nat.lt_size_self _)]
  simp only [shortLogCandidatePointFromCommon, shortLogPointAtOffset,
    shortLogPointAtOffsetFromReduction, ShortLogNearTarget, pow_two,
    targetUnit, Units.ext_iff, Units.val_pow_eq_pow_val]

/-- Internal state of the full candidate selector. -/
private structure ShortLogSelectorState where
  selected : Option Nat
  arithmetic : List NumberTheory.ArithmeticEvent

/-- Visit one slot while retaining the first success and appending that slot's
actual arithmetic.  The option-tag comparison is recorded even after a prior
success, so no candidate can disappear from the execution trace. -/
private def shortLogSelectorStep {N : Nat}
    (state : ShortLogSelectorState) (check : ShortLogCandidateCheckTrace N) :
    ShortLogSelectorState :=
  { selected := retainFirstShortLogCandidate state.selected check.result
    arithmetic :=
      state.arithmetic ++ check.selectorArithmeticFrom state.selected }

/-- Chronological selector arithmetic from an initial accumulated result.
The tag at each slot is derived from the accumulator exactly as it stood
before that slot was visited. -/
private def shortLogSelectorArithmeticFrom {N : Nat} :
    Option Nat → List (ShortLogCandidateCheckTrace N) →
      List NumberTheory.ArithmeticEvent
  | _, [] => []
  | selected, check :: rest =>
      check.selectorArithmeticFrom selected ++
        shortLogSelectorArithmeticFrom
          (retainFirstShortLogCandidate selected check.result) rest

/-- A full-scan selector trace. -/
structure ShortLogSelectorTrace where
  private mk ::
  /-- Arithmetic from every candidate slot and every option-tag check. -/
  arithmetic : List NumberTheory.ArithmeticEvent
  /-- First successful candidate after the complete fold. -/
  selected : Option Nat

/-- Exact schoolbook charge of the full selector execution. -/
def ShortLogSelectorTrace.schoolbookCharge
    (trace : ShortLogSelectorTrace) : Nat :=
  NumberTheory.arithmeticEventListCharge trace.arithmetic

/-- Scan every slot of the exact candidate vector. -/
@[noinline]
def shortLogSelectorTrace {N work : Nat}
    (checks : List.Vector (ShortLogCandidateCheckTrace N) work) :
    ShortLogSelectorTrace :=
  let final := checks.toList.foldl shortLogSelectorStep
    { selected := none, arithmetic := [] }
  .mk final.arithmetic final.selected

/-- The state projection of the full selector fold is the corresponding fold
of candidate results.  The proof is parametric in the list and never unfolds
the concrete corrected-radius offset vector. -/
private theorem shortLogSelectorFold_selected {N : Nat}
    (checks : List (ShortLogCandidateCheckTrace N))
    (state : ShortLogSelectorState) :
    (checks.foldl shortLogSelectorStep state).selected =
      (checks.map (·.result)).foldl retainFirstShortLogCandidate
        state.selected := by
  induction checks generalizing state with
  | nil => rfl
  | cons check rest ih =>
      rw [List.foldl_cons, ih]
      rfl

/-- The arithmetic projection of the selector fold is the concatenation of
every slot's candidate arithmetic and tag check, even after a prior success. -/
private theorem shortLogSelectorFold_arithmetic {N : Nat}
    (checks : List (ShortLogCandidateCheckTrace N))
    (state : ShortLogSelectorState) :
    (checks.foldl shortLogSelectorStep state).arithmetic =
      state.arithmetic ++
        shortLogSelectorArithmeticFrom state.selected checks := by
  induction checks generalizing state with
  | nil => simp [shortLogSelectorArithmeticFrom]
  | cons check rest ih =>
      rw [List.foldl_cons, ih]
      simp [shortLogSelectorStep, shortLogSelectorArithmeticFrom,
        List.append_assoc]

/-- The sealed selector's value projection is the complete result fold. -/
private theorem shortLogSelectorTrace_selected {N work : Nat}
    (checks : List.Vector (ShortLogCandidateCheckTrace N) work) :
    (shortLogSelectorTrace checks).selected =
      (checks.toList.map (·.result)).foldl
        retainFirstShortLogCandidate none := by
  unfold shortLogSelectorTrace
  change
    (checks.toList.foldl shortLogSelectorStep
      { selected := none, arithmetic := [] }).selected = _
  exact shortLogSelectorFold_selected checks.toList
    { selected := none, arithmetic := [] }

/-- The sealed selector records every candidate slot in vector order. -/
theorem shortLogSelectorTrace_arithmetic {N work : Nat}
    (checks : List.Vector (ShortLogCandidateCheckTrace N) work) :
    (shortLogSelectorTrace checks).arithmetic =
      shortLogSelectorArithmeticFrom none checks.toList := by
  unfold shortLogSelectorTrace
  change
    (checks.toList.foldl shortLogSelectorStep
      { selected := none, arithmetic := [] }).arithmetic = _
  simpa using shortLogSelectorFold_arithmetic checks.toList
    { selected := none, arithmetic := [] }

/-- A state-dependent selector whose every slot is bounded by the same
ceiling has total charge at most the number of visited slots times that
ceiling. -/
private theorem shortLogSelectorArithmeticFrom_charge_le {N : Nat}
    (selected : Option Nat)
    (checks : List (ShortLogCandidateCheckTrace N))
    (ceiling : Nat)
    (hbound : ∀ check ∈ checks, ∀ selected,
      NumberTheory.arithmeticEventListCharge
        (check.selectorArithmeticFrom selected) ≤ ceiling) :
    NumberTheory.arithmeticEventListCharge
        (shortLogSelectorArithmeticFrom selected checks) ≤
      checks.length * ceiling := by
  induction checks generalizing selected with
  | nil =>
      simp [shortLogSelectorArithmeticFrom,
        NumberTheory.arithmeticEventListCharge]
  | cons check rest ih =>
      rw [shortLogSelectorArithmeticFrom,
        NumberTheory.arithmeticEventListCharge_append]
      have hcheck := hbound check (by simp) selected
      have hrest :=
        ih (retainFirstShortLogCandidate selected check.result)
          (by
            intro item hmem nextSelected
            exact hbound item (by simp [hmem]) nextSelected)
      simp only [List.length_cons]
      calc
        NumberTheory.arithmeticEventListCharge
              (check.selectorArithmeticFrom selected) +
            NumberTheory.arithmeticEventListCharge
              (shortLogSelectorArithmeticFrom
                (retainFirstShortLogCandidate selected check.result) rest) ≤
            ceiling + rest.length * ceiling :=
          Nat.add_le_add hcheck hrest
        _ = (rest.length + 1) * ceiling := by ring

/-- A selector whose every visited slot has one operand-width ceiling keeps
that same ceiling across the complete chronological scan. -/
private theorem shortLogSelectorArithmeticFrom_maxOperandWidth_le {N : Nat}
    (selected : Option Nat)
    (checks : List (ShortLogCandidateCheckTrace N))
    (ceiling : Nat)
    (hbound : ∀ check ∈ checks, ∀ selected,
      NumberTheory.arithmeticEventListMaxOperandWidth
        (check.selectorArithmeticFrom selected) ≤ ceiling) :
    NumberTheory.arithmeticEventListMaxOperandWidth
        (shortLogSelectorArithmeticFrom selected checks) ≤ ceiling := by
  induction checks generalizing selected with
  | nil =>
      simp [shortLogSelectorArithmeticFrom,
        NumberTheory.arithmeticEventListMaxOperandWidth]
  | cons check rest ih =>
      rw [shortLogSelectorArithmeticFrom,
        NumberTheory.arithmeticEventListMaxOperandWidth_append]
      apply max_le
      · exact hbound check (by simp) selected
      · apply ih (retainFirstShortLogCandidate selected check.result)
        intro item hmem nextSelected
        exact hbound item (by simp [hmem]) nextSelected

/-- Fixed arithmetic schedule for one centered target coordinate. -/
private def shortLogTargetCoordinateArithmetic (m ell : Nat)
    (sample : ShortLogSample m ell) :
    List NumberTheory.ArithmeticEvent :=
  let registerSum := ell + m
  let modulus := 1 <<< registerSum
  let scale := 1 <<< m
  let scaled := scale * sample.2.val
  let reduced := scaled % modulus
  let negated := modulus - reduced
  let negatedReduced := negated % modulus
  let centeredNatural := negatedReduced % modulus
  [ .natMul scale sample.2.val
  , .natMod scaled modulus
  , .natSub modulus reduced
  , .natMod negated modulus
  , .natMod negatedReduced modulus
  , .natMul 2 centeredNatural
  , .natLe (2 * centeredNatural) modulus
  , .intSub centeredNatural modulus ]

/-- Arithmetic used once to construct the public lattice, centered target,
padded fuel, and public target exponent for one two-sample recovery.  Tuple
assembly and casts are projections; every value-changing integer operation is
listed explicitly. -/
def shortLogPairSetupArithmetic {N : Nat} (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    List NumberTheory.ArithmeticEvent :=
  let registerSum := ell + m
  let fuelProduct := 12 * registerSum
  let exponentNumerator := N - 1
  let exponent := exponentNumerator / 2
  ([ NumberTheory.ArithmeticEvent.natAdd ell m
   , NumberTheory.ArithmeticEvent.natShiftLeft 1 registerSum
   , NumberTheory.ArithmeticEvent.natMul 12 registerSum
   , NumberTheory.ArithmeticEvent.natAdd fuelProduct 10
   , NumberTheory.ArithmeticEvent.natSub N 1
   , NumberTheory.ArithmeticEvent.natDiv exponentNumerator 2
   , NumberTheory.ArithmeticEvent.natLog2 exponent
   , NumberTheory.ArithmeticEvent.natShiftLeft 1 m ] :
      List NumberTheory.ArithmeticEvent) ++
    shortLogTargetCoordinateArithmetic m ell samples.1 ++
      shortLogTargetCoordinateArithmetic m ell samples.2

/-- One sealed setup execution shared by all later pair-recovery stages. -/
structure ShortLogPairSetupTrace {N : Nat} (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) where
  private mk ::
  /-- Concrete source-lattice basis. -/
  basis : NumberTheory.IntegerBasis3
  /-- Concrete centered target consumed by nearest-plane reduction. -/
  target : ShortLogLatticePoint
  /-- Padded iteration count consumed by the reducer. -/
  fuel : Nat
  /-- Public exponent `(N-1)/2`. -/
  targetExponent : Nat
  /-- Binary width consumed by modular exponentiation. -/
  targetExponentBits : Nat
  /-- Complete operand-derived setup schedule. -/
  arithmetic : List NumberTheory.ArithmeticEvent
  /-- The stored basis is the canonical basis for these samples. -/
  basis_canonical : basis = shortLogLatticeBasis m ell samples
  /-- The stored target is the canonical centered target for these samples. -/
  target_canonical : target = shortLogLatticeTarget m ell samples
  /-- The stored fuel is the canonical padded LLL schedule. -/
  fuel_canonical : fuel = shortLogRecoveryFuel m ell
  /-- The stored public exponent is derived from the modulus. -/
  targetExponent_canonical : targetExponent = RSA.targetExponent N
  /-- The stored exponent width is derived from that same exponent. -/
  targetExponentBits_canonical :
    targetExponentBits = Nat.size (RSA.targetExponent N)

/-- Construct the unique pair setup from the public modulus, widths, and
actual measured samples. -/
@[noinline]
def shortLogPairSetupTrace {N : Nat} (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    ShortLogPairSetupTrace (N := N) m ell samples :=
  .mk (shortLogLatticeBasis m ell samples)
    (shortLogLatticeTarget m ell samples)
    (shortLogRecoveryFuel m ell)
    (targetExponent N)
    (Nat.size (targetExponent N))
    (shortLogPairSetupArithmetic (N := N) m ell samples)
    rfl rfl rfl rfl rfl

/-- One centered-coordinate setup schedule has linear operand width. -/
private theorem shortLogTargetCoordinateArithmetic_maxOperandWidth_le
    (m ell : Nat) (sample : ShortLogSample m ell) :
    NumberTheory.arithmeticEventListMaxOperandWidth
        (shortLogTargetCoordinateArithmetic m ell sample) ≤
      3 * (ell + m + 1) := by
  let registerSum := ell + m
  let modulus := 1 <<< registerSum
  let scale := 1 <<< m
  let scaled := scale * sample.2.val
  let reduced := scaled % modulus
  let negated := modulus - reduced
  let negatedReduced := negated % modulus
  let centeredNatural := negatedReduced % modulus
  have hregisterPos : 1 ≤ ell + m + 1 := by omega
  have hmodulusSize : Nat.size modulus = registerSum + 1 := by
    simp [modulus, Nat.one_shiftLeft, Nat.size_pow]
  have hscaleSize : Nat.size scale = m + 1 := by
    simp [scale, Nat.one_shiftLeft, Nat.size_pow]
  have hsampleSize : Nat.size sample.2.val ≤ ell := by
    exact Nat.size_le.2 sample.2.isLt
  have hscaleSizeLe : Nat.size scale ≤ ell + m + 1 := by
    rw [hscaleSize]
    omega
  have hmodulusSizeLe : Nat.size modulus ≤ ell + m + 1 := by
    simpa [registerSum] using hmodulusSize.le
  have hsampleSizeLe : Nat.size sample.2.val ≤ ell + m + 1 :=
    hsampleSize.trans (by omega)
  have hscaledSize : Nat.size scaled ≤ ell + m + 1 := by
    exact
      (NumberTheory.natSize_mul_le_add scale sample.2.val).trans (by
        rw [hscaleSize]
        omega)
  have hreducedSize : Nat.size reduced ≤ ell + m + 1 := by
    exact (Nat.size_le_size (Nat.mod_le _ _)).trans hscaledSize
  have hnegatedSize : Nat.size negated ≤ ell + m + 1 := by
    exact
      (Nat.size_le_size (Nat.sub_le modulus reduced)).trans (by
        exact hmodulusSizeLe)
  have hnegatedReducedSize :
      Nat.size negatedReduced ≤ ell + m + 1 := by
    exact (Nat.size_le_size (Nat.mod_le _ _)).trans hnegatedSize
  have hcenteredSize : Nat.size centeredNatural ≤ ell + m + 1 := by
    exact (Nat.size_le_size (Nat.mod_le _ _)).trans hnegatedReducedSize
  have htwiceSize :
      Nat.size (2 * centeredNatural) ≤ 3 * (ell + m + 1) := by
    have htwo : Nat.size 2 = 2 := by decide
    exact
      (NumberTheory.natSize_mul_le_add 2 centeredNatural).trans (by
        rw [htwo]
        omega)
  have htwoSizeLe : Nat.size 2 ≤ 3 * (ell + m + 1) := by
    have htwo : Nat.size 2 = 2 := by decide
    rw [htwo]
    omega
  have natCastMagnitudeBits (value : Nat) :
      NumberTheory.integerMagnitudeBits (value : Int) = Nat.size value := by
    simp [NumberTheory.integerMagnitudeBits]
  apply NumberTheory.arithmeticEventListMaxOperandWidth_le
  intro event hevent
  simp only [shortLogTargetCoordinateArithmetic, List.mem_cons,
    List.not_mem_nil, or_false] at hevent
  rcases hevent with h | h | h | h | h | h | h | h
  · subst event
    have hbase :
        max (Nat.size scale) (Nat.size sample.2.val) ≤ ell + m + 1 :=
      max_le hscaleSizeLe hsampleSizeLe
    exact hbase.trans (by omega)
  · subst event
    have hbase :
        max (Nat.size scaled) (Nat.size modulus) ≤ ell + m + 1 :=
      max_le hscaledSize hmodulusSizeLe
    exact hbase.trans (by omega)
  · subst event
    have hbase :
        max (Nat.size modulus) (Nat.size reduced) ≤ ell + m + 1 :=
      max_le hmodulusSizeLe hreducedSize
    exact hbase.trans (by omega)
  · subst event
    have hbase :
        max (Nat.size negated) (Nat.size modulus) ≤ ell + m + 1 :=
      max_le hnegatedSize hmodulusSizeLe
    exact hbase.trans (by omega)
  · subst event
    have hbase :
        max (Nat.size negatedReduced) (Nat.size modulus) ≤ ell + m + 1 :=
      max_le hnegatedReducedSize hmodulusSizeLe
    exact hbase.trans (by omega)
  · subst event
    have hbase :
        max (Nat.size 2) (Nat.size centeredNatural) ≤
          3 * (ell + m + 1) :=
      max_le htwoSizeLe (hcenteredSize.trans (by omega))
    exact hbase
  · subst event
    exact max_le htwiceSize (hmodulusSizeLe.trans (by omega))
  · subst event
    simp only [NumberTheory.ArithmeticEvent.operandWidth]
    rw [natCastMagnitudeBits, natCastMagnitudeBits]
    exact max_le
      (hcenteredSize.trans (by omega))
      (hmodulusSizeLe.trans (by omega))

/-- The setup schedule stays within a small linear envelope in the complete
public short-log input width. -/
private theorem shortLogPairSetupTrace_maxOperandWidth_le
    {N : Nat} (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    NumberTheory.arithmeticEventListMaxOperandWidth
        (shortLogPairSetupTrace (N := N) m ell samples).arithmetic ≤
      16 * shortLogRecoveryInputBits N m ell := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let events := shortLogPairSetupArithmetic (N := N) m ell samples
  let registerSum := ell + m
  let fuelProduct := 12 * registerSum
  let exponentNumerator := N - 1
  let exponent := exponentNumerator / 2
  have hinputBitsPos : 0 < inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hsizeN : Nat.size N ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hsizeEll : Nat.size ell ≤ inputBits := by
    exact (Nat.size_le.2 ell.lt_two_pow_self).trans (by
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega)
  have hsizeM : Nat.size m ≤ inputBits := by
    exact (Nat.size_le.2 m.lt_two_pow_self).trans (by
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega)
  have hsizeRegisterSum : Nat.size registerSum ≤ inputBits := by
    exact (Nat.size_le.2 registerSum.lt_two_pow_self).trans (by
      dsimp only [inputBits, registerSum, shortLogRecoveryInputBits]
      omega)
  have hsizeModulus : Nat.size (1 <<< registerSum) ≤ inputBits := by
    rw [Nat.one_shiftLeft, Nat.size_pow]
    dsimp only [inputBits, registerSum, shortLogRecoveryInputBits]
    omega
  have hsizeFuelProduct : Nat.size fuelProduct ≤ 5 * inputBits := by
    have hsizeTwelve : Nat.size 12 = 4 := by decide
    exact
      (NumberTheory.natSize_mul_le_add 12 registerSum).trans (by
        rw [hsizeTwelve]
        omega)
  have hsizeExponentNumerator :
      Nat.size exponentNumerator ≤ inputBits := by
    exact
      (Nat.size_le_size (Nat.sub_le N 1)).trans hsizeN
  have hsizeExponent : Nat.size exponent ≤ inputBits := by
    exact
      (Nat.size_le_size (Nat.div_le_self exponentNumerator 2)).trans
        hsizeExponentNumerator
  change NumberTheory.arithmeticEventListMaxOperandWidth events ≤
    16 * inputBits
  apply NumberTheory.arithmeticEventListMaxOperandWidth_le
  intro event hevent
  change event ∈
    ([ .natAdd ell m
     , .natShiftLeft 1 registerSum
     , .natMul 12 registerSum
     , .natAdd fuelProduct 10
     , .natSub N 1
     , .natDiv exponentNumerator 2
     , .natLog2 exponent
     , .natShiftLeft 1 m ] : List NumberTheory.ArithmeticEvent) ++
      (shortLogTargetCoordinateArithmetic m ell samples.1 ++
        shortLogTargetCoordinateArithmetic m ell samples.2) at hevent
  rcases List.mem_append.mp hevent with hprefix | hcoordinates
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hprefix
    rcases hprefix with h | h | h | h | h | h | h | h
    · subst event
      exact (max_le hsizeEll hsizeM).trans (by omega)
    · subst event
      exact (max_le hsizeRegisterSum hsizeModulus).trans (by omega)
    · subst event
      have hsizeTwelve : Nat.size 12 = 4 := by decide
      have hconstant : Nat.size 12 ≤ 5 * inputBits := by
        rw [hsizeTwelve]
        omega
      have hbase :
          max (Nat.size 12) (Nat.size registerSum) ≤ 5 * inputBits :=
        max_le hconstant (hsizeRegisterSum.trans (by omega))
      exact hbase.trans (by omega)
    · subst event
      have hsizeTen : Nat.size 10 = 4 := by decide
      exact (max_le hsizeFuelProduct (by rw [hsizeTen]; omega)).trans
        (by omega)
    · subst event
      exact (max_le hsizeN (by simp; omega)).trans (by omega)
    · subst event
      have htwo : Nat.size 2 = 2 := by decide
      have hconstant : Nat.size 2 ≤ 2 * inputBits := by
        rw [htwo]
        omega
      have hbase :
          max (Nat.size exponentNumerator) (Nat.size 2) ≤
            2 * inputBits :=
        max_le (hsizeExponentNumerator.trans (by omega)) hconstant
      exact hbase.trans (by omega)
    · subst event
      exact hsizeExponent.trans (by omega)
    · subst event
      have hsizeScale : Nat.size (1 <<< m) = m + 1 := by
        simp [Nat.one_shiftLeft, Nat.size_pow]
      have hscaleLe : Nat.size (1 <<< m) ≤ inputBits := by
        rw [hsizeScale]
        dsimp only [inputBits, shortLogRecoveryInputBits]
        omega
      exact (max_le hsizeM hscaleLe).trans (by omega)
  · rcases List.mem_append.mp hcoordinates with hfirst | hsecond
    · exact
        (NumberTheory.ArithmeticEvent.operandWidth_le_listMax hfirst).trans
          ((shortLogTargetCoordinateArithmetic_maxOperandWidth_le
            m ell samples.1).trans (by
              dsimp only [inputBits, shortLogRecoveryInputBits]
              omega))
    · exact
        (NumberTheory.ArithmeticEvent.operandWidth_le_listMax hsecond).trans
          ((shortLogTargetCoordinateArithmetic_maxOperandWidth_le
            m ell samples.2).trans (by
              dsimp only [inputBits, shortLogRecoveryInputBits]
              omega))

/-- The complete setup schedule has a uniform cubic schoolbook envelope in
the public short-log input bit size. -/
theorem shortLogPairSetupTrace_schoolbookCharge_le
    {N : Nat} (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    NumberTheory.arithmeticEventListCharge
        (shortLogPairSetupTrace (N := N) m ell samples).arithmetic ≤
      2 ^ 16 * shortLogRecoveryInputBits N m ell ^ 3 := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let events := shortLogPairSetupArithmetic (N := N) m ell samples
  let registerSum := ell + m
  let fuelProduct := 12 * registerSum
  let exponentNumerator := N - 1
  let exponent := exponentNumerator / 2
  have hinputBitsPos : 1 ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hsizeN : Nat.size N ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hsizeEll : Nat.size ell ≤ inputBits := by
    exact (Nat.size_le.2 ell.lt_two_pow_self).trans (by
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega)
  have hsizeM : Nat.size m ≤ inputBits := by
    exact (Nat.size_le.2 m.lt_two_pow_self).trans (by
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega)
  have hsizeRegisterSum : Nat.size registerSum ≤ inputBits := by
    exact (Nat.size_le.2 registerSum.lt_two_pow_self).trans (by
      dsimp only [inputBits, registerSum, shortLogRecoveryInputBits]
      omega)
  have hsizeModulus : Nat.size (1 <<< registerSum) ≤ inputBits := by
    rw [Nat.one_shiftLeft, Nat.size_pow]
    dsimp only [inputBits, registerSum, shortLogRecoveryInputBits]
    omega
  have hsizeFuelProduct : Nat.size fuelProduct ≤ 5 * inputBits := by
    have hsizeTwelve : Nat.size 12 = 4 := by decide
    exact
      (NumberTheory.natSize_mul_le_add 12 registerSum).trans (by
        rw [hsizeTwelve]
        omega)
  have hsizeExponentNumerator :
      Nat.size exponentNumerator ≤ inputBits := by
    exact
      (Nat.size_le_size (Nat.sub_le N 1)).trans hsizeN
  have hsizeExponent : Nat.size exponent ≤ inputBits := by
    exact
      (Nat.size_le_size (Nat.div_le_self exponentNumerator 2)).trans
        hsizeExponentNumerator
  have hwidth :
      NumberTheory.arithmeticEventListMaxOperandWidth events ≤
        16 * inputBits := by
    apply NumberTheory.arithmeticEventListMaxOperandWidth_le
    intro event hevent
    change event ∈
      ([ .natAdd ell m
       , .natShiftLeft 1 registerSum
       , .natMul 12 registerSum
       , .natAdd fuelProduct 10
       , .natSub N 1
       , .natDiv exponentNumerator 2
       , .natLog2 exponent
       , .natShiftLeft 1 m ] : List NumberTheory.ArithmeticEvent) ++
        (shortLogTargetCoordinateArithmetic m ell samples.1 ++
          shortLogTargetCoordinateArithmetic m ell samples.2) at hevent
    rcases List.mem_append.mp hevent with hprefix | hcoordinates
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hprefix
      rcases hprefix with h | h | h | h | h | h | h | h
      · subst event
        exact (max_le hsizeEll hsizeM).trans (by omega)
      · subst event
        exact (max_le hsizeRegisterSum hsizeModulus).trans (by omega)
      · subst event
        have hsizeTwelve : Nat.size 12 = 4 := by decide
        have hconstant : Nat.size 12 ≤ 5 * inputBits := by
          rw [hsizeTwelve]
          omega
        have hbase :
            max (Nat.size 12) (Nat.size registerSum) ≤ 5 * inputBits :=
          max_le hconstant (hsizeRegisterSum.trans (by omega))
        exact hbase.trans (by omega)
      · subst event
        have hsizeTen : Nat.size 10 = 4 := by decide
        exact (max_le hsizeFuelProduct (by rw [hsizeTen]; omega)).trans
          (by omega)
      · subst event
        exact (max_le hsizeN (by simp; omega)).trans (by omega)
      · subst event
        have htwo : Nat.size 2 = 2 := by decide
        have hconstant : Nat.size 2 ≤ 2 * inputBits := by
          rw [htwo]
          omega
        have hbase :
            max (Nat.size exponentNumerator) (Nat.size 2) ≤
              2 * inputBits :=
          max_le (hsizeExponentNumerator.trans (by omega)) hconstant
        exact hbase.trans (by omega)
      · subst event
        exact hsizeExponent.trans (by omega)
      · subst event
        have hsizeScale : Nat.size (1 <<< m) = m + 1 := by
          simp [Nat.one_shiftLeft, Nat.size_pow]
        have hscaleLe : Nat.size (1 <<< m) ≤ inputBits := by
          rw [hsizeScale]
          dsimp only [inputBits, shortLogRecoveryInputBits]
          omega
        exact (max_le hsizeM hscaleLe).trans (by omega)
    · rcases List.mem_append.mp hcoordinates with hfirst | hsecond
      · exact
          (NumberTheory.ArithmeticEvent.operandWidth_le_listMax hfirst).trans
            ((shortLogTargetCoordinateArithmetic_maxOperandWidth_le
              m ell samples.1).trans (by
                dsimp only [inputBits, shortLogRecoveryInputBits]
                omega))
      · exact
          (NumberTheory.ArithmeticEvent.operandWidth_le_listMax hsecond).trans
            ((shortLogTargetCoordinateArithmetic_maxOperandWidth_le
              m ell samples.2).trans (by
                dsimp only [inputBits, shortLogRecoveryInputBits]
                omega))
  have hlength : events.length = 24 := by
    simp [events, shortLogPairSetupArithmetic,
      shortLogTargetCoordinateArithmetic]
  have hwidthSucc : 16 * inputBits + 1 ≤ 17 * inputBits := by omega
  have hsquareCube : inputBits ^ 2 ≤ inputBits ^ 3 := by
    calc
      inputBits ^ 2 = inputBits ^ 2 * 1 := by ring
      _ ≤ inputBits ^ 2 * inputBits :=
        Nat.mul_le_mul_left _ hinputBitsPos
      _ = inputBits ^ 3 := by ring
  change NumberTheory.arithmeticEventListCharge events ≤ _
  calc
    NumberTheory.arithmeticEventListCharge events ≤
        4 * events.length *
          (NumberTheory.arithmeticEventListMaxOperandWidth events + 1) ^ 2 :=
      NumberTheory.arithmeticEventListCharge_le events
    _ ≤ 4 * 24 * (16 * inputBits + 1) ^ 2 := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 hlength.le)
        (Nat.pow_le_pow_left (Nat.add_le_add_right hwidth 1) 2)
    _ ≤ 4 * 24 * (17 * inputBits) ^ 2 :=
      Nat.mul_le_mul_left (4 * 24)
        (Nat.pow_le_pow_left hwidthSucc 2)
    _ = 27_744 * inputBits ^ 2 := by ring
    _ ≤ 27_744 * inputBits ^ 3 :=
      Nat.mul_le_mul_left _ hsquareCube
    _ ≤ 2 ^ 16 * inputBits ^ 3 :=
      Nat.mul_le_mul_right _ (by norm_num)

/-- One complete two-sample recovery execution.  Every stage and the final
factor are owned by one sealed object. -/
structure ShortLogPairRecoveryTrace {N : Nat} (m ell : Nat)
    (samples : ShortLogSample m ell × ShortLogSample m ell) where
  private mk ::
  /-- Unique public/setup arithmetic shared by every downstream stage. -/
  setup : ShortLogPairSetupTrace (N := N) m ell samples
  /-- Unique padded LLL execution for this pair. -/
  reduction : NumberTheory.LatticeReductionTrace3
  /-- Unique exact nearest-plane execution for this pair. -/
  nearest : NumberTheory.NearestPlaneTrace3 reduction.output
    (shortLogLatticeTarget m ell samples)
  /-- Target group power computed once for all candidate slots. -/
  targetPower : NumberTheory.ModularPowerTrace N
  /-- Exactly one check for every canonical coefficient offset. -/
  checks : List.Vector (ShortLogCandidateCheckTrace N)
    (NumberTheory.coefficientOffsetBoxWork3
      NumberTheory.nearestPlaneCoefficientBounds3)
  /-- Full-scan first-success selector. -/
  selector : ShortLogSelectorTrace
  /-- Unique quadratic factor-recovery execution indexed by the selected log. -/
  quadratic : QuadraticFactorRecoveryExecution N selector.selected

/-- Complete arithmetic is the fixed concatenation of the five stored stages
and the uniquely derived quadratic stage. -/
def ShortLogPairRecoveryTrace.arithmetic {N m ell : Nat}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (trace : ShortLogPairRecoveryTrace (N := N) m ell samples) :
    List NumberTheory.ArithmeticEvent :=
  trace.setup.arithmetic ++ trace.reduction.arithmetic ++
    trace.nearest.arithmetic ++
    trace.targetPower.arithmetic ++ trace.selector.arithmetic ++
    trace.quadratic.trace.arithmetic

/-- Exact schoolbook charge of the complete pair execution. -/
def ShortLogPairRecoveryTrace.schoolbookCharge {N m ell : Nat}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (trace : ShortLogPairRecoveryTrace (N := N) m ell samples) : Nat :=
  NumberTheory.arithmeticEventListCharge trace.arithmetic

/-- Largest arithmetic-operand width encountered by one sealed pair recovery
execution. -/
def ShortLogPairRecoveryTrace.maxOperandWidth {N m ell : Nat}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (trace : ShortLogPairRecoveryTrace (N := N) m ell samples) : Nat :=
  NumberTheory.arithmeticEventListMaxOperandWidth trace.arithmetic

/-- Pair charge is exactly the sum of the unique setup, reduction,
nearest-center, target-power, full-selector, and quadratic stages. -/
theorem ShortLogPairRecoveryTrace.schoolbookCharge_eq {N m ell : Nat}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (trace : ShortLogPairRecoveryTrace (N := N) m ell samples) :
    trace.schoolbookCharge =
      NumberTheory.arithmeticEventListCharge trace.setup.arithmetic +
        trace.reduction.schoolbookCharge + trace.nearest.schoolbookCharge +
          trace.targetPower.schoolbookCharge +
            trace.selector.schoolbookCharge +
              trace.quadratic.trace.schoolbookCharge := by
  simp [ShortLogPairRecoveryTrace.schoolbookCharge,
    ShortLogPairRecoveryTrace.arithmetic,
    NumberTheory.LatticeReductionTrace3.schoolbookCharge,
    NumberTheory.NearestPlaneTrace3.schoolbookCharge,
    NumberTheory.ModularPowerTrace.schoolbookCharge,
    ShortLogSelectorTrace.schoolbookCharge,
    QuadraticFactorRecoveryTrace.schoolbookCharge, Nat.add_assoc]

/-- The factor result is the unique quadratic projection of this pair trace. -/
def ShortLogPairRecoveryTrace.result {N m ell : Nat}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (trace : ShortLogPairRecoveryTrace (N := N) m ell samples) : Option Nat :=
  trace.quadratic.trace.result

/-- Canonical-stage ownership laws for one opaque pair execution.  Every law
is phrased relative to fields of the same trace, avoiding dependent transports
while fixing all value and arithmetic projections to the unique builder. -/
private structure ShortLogPairRecoverySpec {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (trace : ShortLogPairRecoveryTrace (N := N) m ell samples) : Prop where
  setup_eq : trace.setup = shortLogPairSetupTrace m ell samples
  reduction_eq : trace.reduction = shortLogRecoveryTrace m ell samples
  nearest_eq : trace.nearest = NumberTheory.nearestPlaneTrace3
    trace.reduction.output (shortLogLatticeTarget m ell samples)
  targetPower_eq : trace.targetPower = NumberTheory.modularPowerTrace
    (Nat.size (targetExponent N)) generator.val (targetExponent N)
  checks_eq : trace.checks = shortLogCandidateTraceVectorFromCommon
    m ell generator samples trace.reduction trace.nearest trace.targetPower
  selector_eq : trace.selector = shortLogSelectorTrace trace.checks

/-- Internal implementation of the complete pair-recovery trace and its
ownership certificate.  Constructing the subtype in the same local `let`
context keeps the giant fixed-length vector shared while all laws are checked. -/
@[noinline]
private def shortLogPairRecoveryTraceImpl {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    { trace : ShortLogPairRecoveryTrace (N := N) m ell samples //
      ShortLogPairRecoverySpec m ell generator samples trace } := by
  let setup := shortLogPairSetupTrace (N := N) m ell samples
  let reduction := NumberTheory.lllReduce3WithFuel
    setup.fuel setup.basis
  let nearest : NumberTheory.NearestPlaneTrace3 reduction.output
      (shortLogLatticeTarget m ell samples) :=
    setup.target_canonical ▸
      NumberTheory.nearestPlaneTrace3 reduction.output setup.target
  let targetPower := NumberTheory.modularPowerTrace
    setup.targetExponentBits generator.val setup.targetExponent
  let checks := shortLogCandidateTraceVectorFromCommon m ell generator samples
    reduction nearest targetPower
  let selector := shortLogSelectorTrace checks
  let quadratic := quadraticFactorRecoveryExecution N selector.selected
  refine ⟨.mk setup reduction nearest targetPower checks selector quadratic, ?_⟩
  exact {
    setup_eq := rfl
    reduction_eq := rfl
    nearest_eq := rfl
    targetPower_eq := rfl
    checks_eq := rfl
    selector_eq := rfl
  }

/-- The single opaque execution boundary for pair recovery. -/
private structure ShortLogPairRecoveryProgram where
  run : {N m ell : Nat} → (generator : (ZMod N)ˣ) →
    (samples : ShortLogSample m ell × ShortLogSample m ell) →
      ShortLogPairRecoveryTrace (N := N) m ell samples
  run_spec : ∀ {N m ell : Nat} (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell),
    ShortLogPairRecoverySpec m ell generator samples (run generator samples)

/-- The unique canonical pair implementation and all stored-stage ownership
laws are checked once at this opacity boundary.  Derived quadratic, arithmetic,
and result projections cannot be supplied independently. -/
private opaque shortLogPairRecoveryProgram : ShortLogPairRecoveryProgram := {
  run := fun generator samples =>
    (shortLogPairRecoveryTraceImpl _ _ generator samples).1
  run_spec := fun generator samples =>
    (shortLogPairRecoveryTraceImpl _ _ generator samples).2
}

/-- Build the complete pair-recovery trace from public parameters and the two
actual samples through the unique opaque execution boundary. -/
def shortLogPairRecoveryTrace {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    ShortLogPairRecoveryTrace (N := N) m ell samples :=
  shortLogPairRecoveryProgram.run generator samples

/-- Ownership certificate for the public pair trace. -/
private theorem shortLogPairRecoveryTrace_spec {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    ShortLogPairRecoverySpec m ell generator samples
      (shortLogPairRecoveryTrace m ell generator samples) :=
  shortLogPairRecoveryProgram.run_spec generator samples

/-- The complete 404,685-slot selector has cubic schoolbook charge in the
public short-log input envelope. -/
private theorem shortLogPairRecoveryTrace_selector_charge_le
    {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (hN : 0 < N) :
    (shortLogPairRecoveryTrace m ell generator samples).selector.schoolbookCharge ≤
      2 ^ 74 * shortLogRecoveryInputBits N m ell ^ 3 := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let offsets := NumberTheory.coefficientOffsetList3
    NumberTheory.nearestPlaneCoefficientBounds3
  let reduction := shortLogRecoveryTrace m ell samples
  let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
    (shortLogLatticeTarget m ell samples)
  let targetPower := NumberTheory.modularPowerTrace
    (Nat.size (targetExponent N)) generator.val (targetExponent N)
  let slotCheck := fun offset =>
    shortLogCandidateCheckTraceFromCommon m ell generator samples reduction
      nearest targetPower offset
  let mappedChecks := offsets.map slotCheck
  have hslot : ∀ offset ∈ offsets, ∀ selected,
      NumberTheory.arithmeticEventListCharge
          ((slotCheck offset).selectorArithmeticFrom selected) ≤
        2 ^ 55 * inputBits ^ 3 := by
    intro offset hoffset selected
    simpa [offsets, slotCheck, reduction, nearest, targetPower, inputBits] using
      shortLogCandidateCheckTraceFromCommon_selectorArithmeticFrom_charge_le
        m ell generator samples hoffset selected hN
  have hrecursive :
      NumberTheory.arithmeticEventListCharge
          (shortLogSelectorArithmeticFrom none mappedChecks) ≤
        mappedChecks.length * (2 ^ 55 * inputBits ^ 3) := by
    have hbound : ∀ check ∈ mappedChecks, ∀ selected,
        NumberTheory.arithmeticEventListCharge
            (check.selectorArithmeticFrom selected) ≤
          2 ^ 55 * inputBits ^ 3 := by
      intro check hcheck selected
      have hmapped : check ∈ offsets.map slotCheck := by
        simpa [mappedChecks] using hcheck
      rcases List.mem_map.mp hmapped with ⟨offset, hoffset, rfl⟩
      exact hslot offset hoffset selected
    exact shortLogSelectorArithmeticFrom_charge_le
      (N := N) none mappedChecks
        (2 ^ 55 * inputBits ^ 3) hbound
  have hwork : offsets.length ≤ 2 ^ 19 := by
    rw [show offsets.length =
      NumberTheory.coefficientOffsetBoxWork3
        NumberTheory.nearestPlaneCoefficientBounds3 by
      simp [offsets, NumberTheory.length_coefficientOffsetList3]]
    rw [NumberTheory.nearestPlaneCoefficientBounds3_work]
    norm_num
  have htrace :
      (shortLogPairRecoveryTrace m ell generator samples).selector.arithmetic =
        shortLogSelectorArithmeticFrom none mappedChecks := by
    have hspec := shortLogPairRecoveryTrace_spec m ell generator samples
    rw [hspec.selector_eq, shortLogSelectorTrace_arithmetic, hspec.checks_eq,
      hspec.targetPower_eq, hspec.nearest_eq, hspec.reduction_eq]
    simp only [shortLogCandidateTraceVectorFromCommon,
      NumberTheory.toList_mapCoefficientOffsetVector3]
    change shortLogSelectorArithmeticFrom none (offsets.map slotCheck) =
      shortLogSelectorArithmeticFrom none mappedChecks
    rw [show mappedChecks = offsets.map slotCheck by rfl]
  rw [ShortLogSelectorTrace.schoolbookCharge, htrace]
  calc
    NumberTheory.arithmeticEventListCharge
        (shortLogSelectorArithmeticFrom none mappedChecks) ≤
        mappedChecks.length * (2 ^ 55 * inputBits ^ 3) := hrecursive
    _ = offsets.length * (2 ^ 55 * inputBits ^ 3) := by
      rw [show mappedChecks.length = offsets.length by
        simp [mappedChecks]]
    _ ≤ 2 ^ 19 * (2 ^ 55 * inputBits ^ 3) :=
      Nat.mul_le_mul_right _ hwork
    _ = 2 ^ 74 * inputBits ^ 3 := by ring

/-- The full fixed-order selector retains the one-slot operand-width envelope:
the scan grows arithmetic length but never widens an operand. -/
private theorem shortLogPairRecoveryTrace_selector_maxOperandWidth_le
    {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (hN : 0 < N) :
    NumberTheory.arithmeticEventListMaxOperandWidth
        (shortLogPairRecoveryTrace m ell generator samples).selector.arithmetic ≤
      2 ^ 20 * shortLogRecoveryInputBits N m ell := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let offsets := NumberTheory.coefficientOffsetList3
    NumberTheory.nearestPlaneCoefficientBounds3
  let reduction := shortLogRecoveryTrace m ell samples
  let nearest := NumberTheory.nearestPlaneTrace3 reduction.output
    (shortLogLatticeTarget m ell samples)
  let targetPower := NumberTheory.modularPowerTrace
    (Nat.size (targetExponent N)) generator.val (targetExponent N)
  let slotCheck := fun offset =>
    shortLogCandidateCheckTraceFromCommon m ell generator samples reduction
      nearest targetPower offset
  let mappedChecks := offsets.map slotCheck
  have hslot : ∀ offset ∈ offsets, ∀ selected,
      NumberTheory.arithmeticEventListMaxOperandWidth
          ((slotCheck offset).selectorArithmeticFrom selected) ≤
        2 ^ 20 * inputBits := by
    intro offset hoffset selected
    simpa [offsets, slotCheck, reduction, nearest, targetPower, inputBits] using
      shortLogCandidateCheckTraceFromCommon_selectorArithmeticFrom_maxOperandWidth_le
        m ell generator samples hoffset selected hN
  have hrecursive :
      NumberTheory.arithmeticEventListMaxOperandWidth
          (shortLogSelectorArithmeticFrom none mappedChecks) ≤
        2 ^ 20 * inputBits := by
    have hbound : ∀ check ∈ mappedChecks, ∀ selected,
        NumberTheory.arithmeticEventListMaxOperandWidth
            (check.selectorArithmeticFrom selected) ≤
          2 ^ 20 * inputBits := by
      intro check hcheck selected
      have hmapped : check ∈ offsets.map slotCheck := by
        simpa [mappedChecks] using hcheck
      rcases List.mem_map.mp hmapped with ⟨offset, hoffset, rfl⟩
      exact hslot offset hoffset selected
    exact shortLogSelectorArithmeticFrom_maxOperandWidth_le
      (N := N) none mappedChecks (2 ^ 20 * inputBits) hbound
  have htrace :
      (shortLogPairRecoveryTrace m ell generator samples).selector.arithmetic =
        shortLogSelectorArithmeticFrom none mappedChecks := by
    have hspec := shortLogPairRecoveryTrace_spec m ell generator samples
    rw [hspec.selector_eq, shortLogSelectorTrace_arithmetic, hspec.checks_eq,
      hspec.targetPower_eq, hspec.nearest_eq, hspec.reduction_eq]
    simp only [shortLogCandidateTraceVectorFromCommon,
      NumberTheory.toList_mapCoefficientOffsetVector3]
    change shortLogSelectorArithmeticFrom none (offsets.map slotCheck) =
      shortLogSelectorArithmeticFrom none mappedChecks
    rw [show mappedChecks = offsets.map slotCheck by rfl]
  rw [htrace]
  exact hrecursive

/-- Complete fixed-order validation trace projected from the same pair
execution that supplies the result. -/
def shortLogCandidateChecks {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    List (Option Nat) :=
  (shortLogPairRecoveryTrace m ell generator samples).checks.toList.map
    (·.result)

/-- The complete trace is definitionally the canonical map of the
proof-facing offset checker. -/
theorem shortLogCandidateChecks_eq_map {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    shortLogCandidateChecks m ell generator samples =
      (NumberTheory.coefficientOffsetList3
        NumberTheory.nearestPlaneCoefficientBounds3).map
          (shortLogCandidateAtOffset m ell generator samples) := by
  have hspec := shortLogPairRecoveryTrace_spec m ell generator samples
  rw [shortLogCandidateChecks, hspec.checks_eq]
  simp only [shortLogCandidateTraceVectorFromCommon,
    NumberTheory.toList_mapCoefficientOffsetVector3, List.map_map]
  apply List.map_congr_left
  intro offset _hoffset
  rw [hspec.targetPower_eq, hspec.nearest_eq, hspec.reduction_eq]
  rfl

/-- All validated candidates, in the canonical coefficient-scan order. -/
def shortLogCandidateList {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) : List Nat :=
  (shortLogCandidateChecks m ell generator samples).filterMap id

/-- Select the first result produced by the complete fixed-order fold. -/
def recoverShortLogFromPair {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) : Option Nat :=
  (shortLogPairRecoveryTrace m ell generator samples).selector.selected

/-- The public short-log result is the selector projection of the unique pair
execution.  Downstream proofs use this bridge instead of unfolding the full
fixed-length trace. -/
theorem recoverShortLogFromPair_eq_selector {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    recoverShortLogFromPair m ell generator samples =
      (shortLogPairRecoveryTrace m ell generator samples).selector.selected := by
  rfl

/-- Recover an RSA factor from one actual pair of short-log samples. -/
def recoverFactorFromShortLogPair {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) : Option Nat :=
  (shortLogPairRecoveryTrace m ell generator samples).result

/-- The public factor result is the quadratic projection of the short logarithm
selected by the same sealed recovery program. -/
theorem recoverFactorFromShortLogPair_eq_run {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    recoverFactorFromShortLogPair m ell generator samples =
      (quadraticFactorRecoveryTrace N
        (recoverShortLogFromPair m ell generator samples)).result := by
  unfold recoverFactorFromShortLogPair ShortLogPairRecoveryTrace.result
  rw [(shortLogPairRecoveryTrace m ell generator samples).quadratic.canonical]
  rfl

/-- The selected result is definitionally the complete fold of the check
trace stored in the same recovery object. -/
theorem shortLogPairRecoveryTrace_selected_fold {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogPairRecoveryTrace m ell generator samples).selector.selected =
      (shortLogCandidateChecks m ell generator samples).foldl
        retainFirstShortLogCandidate none := by
  rw [(shortLogPairRecoveryTrace_spec m ell generator samples).selector_eq]
  rw [shortLogSelectorTrace_selected]
  rfl

/-- The candidate list is the successful-value projection of the check trace
stored in the same recovery object. -/
theorem shortLogCandidateList_eq_checks_filterMap {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    shortLogCandidateList m ell generator samples =
    (shortLogCandidateChecks m ell generator samples).filterMap id := by
  rfl

end SealedPairRecoveryTrace

/-- Folding with `retainFirstShortLogCandidate` agrees with taking the head of
the validated-candidate list, while its recursion still traverses the complete
check list. -/
theorem foldl_retainFirstShortLogCandidate (checks : List (Option Nat))
    (selected : Option Nat) :
    checks.foldl retainFirstShortLogCandidate selected =
      match selected with
      | some candidate => some candidate
      | none => (checks.filterMap id).head? := by
  induction checks generalizing selected with
  | nil => cases selected <;> rfl
  | cons checked rest ih =>
      rw [List.foldl_cons, ih]
      cases selected <;> cases checked <;>
        simp [retainFirstShortLogCandidate]

/-- The selected trace result is exactly the first validated candidate. -/
theorem shortLogPairRecoveryTrace_selected {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogPairRecoveryTrace m ell generator samples).selector.selected =
      (shortLogCandidateList m ell generator samples).head? := by
  rw [shortLogPairRecoveryTrace_selected_fold,
    shortLogCandidateList_eq_checks_filterMap]
  exact foldl_retainFirstShortLogCandidate _ none

/-- The complete validation trace has the exact constant length of the
three-dimensional coefficient box. -/
theorem shortLogCandidateChecks_length {N : Nat} (m ell : Nat)
    (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell) :
    (shortLogCandidateChecks m ell generator samples).length = 85 * 69 ^ 2 := by
  rw [shortLogCandidateChecks_eq_map, List.length_map,
    NumberTheory.length_coefficientOffsetList3,
    NumberTheory.nearestPlaneCoefficientBounds3_work]

/-- Every offset-generated point belongs to the original source lattice. -/
theorem shortLogPointAtOffset_member
    {m ell : Nat} {samples : ShortLogSample m ell × ShortLogSample m ell}
    (offset : NumberTheory.IntegerPoint3) :
    ShortLogLatticeMember m ell samples
      (shortLogPointAtOffset m ell samples offset) := by
  have houtputSpan : ∃ coefficients,
      (shortLogRecoveryTrace m ell samples).output.linearCombination
          coefficients = shortLogPointAtOffset m ell samples offset := by
    let basis := (shortLogRecoveryTrace m ell samples).output
    let center := basis.nearestPlaneCoefficientCenter
      (shortLogLatticeTarget m ell samples)
    refine ⟨center.add offset, ?_⟩
    rw [shortLogPointAtOffset_eq]
  have hsourceSpan :=
    (shortLogRecoveryTrace_spans m ell samples
      (shortLogPointAtOffset m ell samples offset)).mpr houtputSpan
  rcases hsourceSpan with ⟨coefficients, hcoefficients⟩
  refine ⟨coefficients, ?_⟩
  rw [← shortLogLatticeBasis_linearCombination]
  exact hcoefficients

/-- A successful offset check carries exactly the full validated-point
contract used by the semantic uniqueness theorem. -/
theorem shortLogCandidateAtOffset_some_validated
    {N m ell candidate : Nat} {generator : (ZMod N)ˣ}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    {offset : NumberTheory.IntegerPoint3}
    (hresult : shortLogCandidateAtOffset m ell generator samples offset =
      some candidate) :
    ShortLogValidatedPoint m ell generator samples
        (shortLogPointAtOffset m ell samples offset) ∧
      (shortLogPointAtOffset m ell samples offset).2.2.toNat = candidate := by
  rw [shortLogCandidateAtOffset_eq] at hresult
  dsimp only at hresult
  split at hresult
  next hvalid =>
    simp only [Option.some.injEq] at hresult
    exact ⟨⟨shortLogPointAtOffset_member offset, hvalid⟩, hresult⟩
  next _ => simp at hresult

/-- Below the generator order, the public target relation admits at most one
short logarithm.  This is the uniqueness condition needed to turn the closed
candidate selector into a semantic recovery theorem. -/
theorem ShortLogPairCandidate.unique_of_order
    {N m ell : Nat} {generator : (ZMod N)ˣ}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    {first second : Nat} (horder : 2 ^ m ≤ orderOf generator)
    (hfirst : ShortLogPairCandidate m ell generator samples first)
    (hsecond : ShortLogPairCandidate m ell generator samples second) :
    first = second := by
  have hfirstOrder : first < orderOf generator :=
    hfirst.2.1.trans_le horder
  have hsecondOrder : second < orderOf generator :=
    hsecond.2.1.trans_le horder
  have hpowers : generator ^ first = generator ^ second :=
    hfirst.2.2.1.trans hsecond.2.2.1.symm
  have hmods : first % orderOf generator = second % orderOf generator :=
    pow_inj_mod.mp hpowers
  simpa [Nat.mod_eq_of_lt hfirstOrder, Nat.mod_eq_of_lt hsecondOrder]
    using hmods

/-- Every validated searched point has the same logarithm as a semantic source
candidate whenever the advertised short range lies below the generator order. -/
theorem ShortLogValidatedPoint.toNat_eq_candidate
    {N m ell secret : Nat} {generator : (ZMod N)ˣ}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    {point : ShortLogLatticePoint}
    (horder : 2 ^ m ≤ orderOf generator)
    (hcandidate : ShortLogPairCandidate m ell generator samples secret)
    (hpoint : ShortLogValidatedPoint m ell generator samples point) :
    point.2.2.toNat = secret := by
  have hpointNonneg : 0 ≤ point.2.2 := le_of_lt hpoint.2.2.1
  have hpointLt : point.2.2.toNat < 2 ^ m := by
    rw [← Int.ofNat_lt]
    simpa [Int.toNat_of_nonneg hpointNonneg] using hpoint.2.2.2.1
  have hpointOrder : point.2.2.toNat < orderOf generator :=
    hpointLt.trans_le horder
  have hsecretOrder : secret < orderOf generator :=
    hcandidate.2.1.trans_le horder
  have hpowers : generator ^ point.2.2.toNat = generator ^ secret :=
    hpoint.2.2.2.2.trans hcandidate.2.2.1.symm
  have hmods : point.2.2.toNat % orderOf generator =
      secret % orderOf generator := pow_inj_mod.mp hpowers
  simpa [Nat.mod_eq_of_lt hpointOrder, Nat.mod_eq_of_lt hsecretOrder]
    using hmods

/-- A semantic source candidate occurs in the fixed-order executable check
trace. -/
theorem shortLogCandidate_mem
    {N m ell secret : Nat} {generator : (ZMod N)ˣ}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hfeasible : ShortLogRecoveryFeasible m ell samples)
    (hcandidate : ShortLogPairCandidate m ell generator samples secret) :
    secret ∈ shortLogCandidateList m ell generator samples := by
  have hmember := shortLogWitnessPoint_mem m ell secret samples
  have hnear := shortLogWitnessPoint_near_of_good hcandidate.1
    hcandidate.2.1 hcandidate.2.2.2.1 hcandidate.2.2.2.2
  have hsearch := shortLogNearLatticePoints_complete
    hfeasible.1 hfeasible.2.1 hmember hnear
  rw [shortLogNearLatticePoints, Finset.mem_filter] at hsearch
  rcases (NumberTheory.mem_enumerateNearbyPoints3.mp hsearch.1).2 with
    ⟨offset, hoffset, hpoint⟩
  have hoffsetList : offset ∈ NumberTheory.coefficientOffsetList3
      NumberTheory.nearestPlaneCoefficientBounds3 := by
    rw [NumberTheory.mem_coefficientOffsetList3]
    exact hoffset
  have hpoint' : shortLogPointAtOffset m ell samples offset =
      shortLogWitnessPoint m ell secret samples := by
    rw [shortLogPointAtOffset_eq]
    exact hpoint
  have hvalidated : ShortLogValidatedPoint m ell generator samples
      (shortLogWitnessPoint m ell secret samples) := by
    refine ⟨hmember, hnear, ?_, ?_, ?_⟩
    · change (0 : Int) < (secret : Int)
      exact_mod_cast hcandidate.1
    · change (secret : Int) < (2 ^ m : Nat)
      exact_mod_cast hcandidate.2.1
    · simpa [shortLogWitnessPoint] using hcandidate.2.2.1
  have hcheck : shortLogCandidateAtOffset m ell generator samples offset =
      some secret := by
    rw [shortLogCandidateAtOffset_eq, hpoint']
    rw [if_pos hvalidated.2]
    simp [shortLogWitnessPoint]
  rw [shortLogCandidateList, List.mem_filterMap]
  refine ⟨some secret, ?_, rfl⟩
  rw [shortLogCandidateChecks_eq_map, List.mem_map]
  exact ⟨offset, hoffsetList, hcheck⟩

/-- Every item retained by the executable filter comes from one fully
validated lattice point in the same fixed scan. -/
theorem shortLogCandidateList_member_validated
    {N m ell candidate : Nat} {generator : (ZMod N)ˣ}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hmember : candidate ∈ shortLogCandidateList m ell generator samples) :
    ∃ offset,
      shortLogCandidateAtOffset m ell generator samples offset =
          some candidate ∧
        ShortLogValidatedPoint m ell generator samples
          (shortLogPointAtOffset m ell samples offset) ∧
        (shortLogPointAtOffset m ell samples offset).2.2.toNat = candidate := by
  rw [shortLogCandidateList, List.mem_filterMap] at hmember
  rcases hmember with ⟨checked, hchecked, hvalue⟩
  simp only [id_eq] at hvalue
  subst checked
  rw [shortLogCandidateChecks_eq_map, List.mem_map] at hchecked
  rcases hchecked with ⟨offset, _hoffset, hresult⟩
  refine ⟨offset, hresult, ?_⟩
  exact shortLogCandidateAtOffset_some_validated hresult

/-- Any value selected by the full canonical scan lies inside the advertised
short-log range. -/
theorem shortLogPairRecoveryTrace_selected_lt
    {N m ell candidate : Nat} (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (hselected :
      (shortLogPairRecoveryTrace m ell generator samples).selector.selected =
        some candidate) :
    candidate < 2 ^ m := by
  rw [shortLogPairRecoveryTrace_selected] at hselected
  cases hlist : shortLogCandidateList m ell generator samples with
  | nil => simp [hlist] at hselected
  | cons head tail =>
      simp [hlist] at hselected
      subst head
      have hmember :
          candidate ∈ shortLogCandidateList m ell generator samples := by
        simp [hlist]
      rcases shortLogCandidateList_member_validated hmember with
        ⟨offset, _hresult, hvalidated, hvalue⟩
      have hnonneg :
          0 ≤ (shortLogPointAtOffset m ell samples offset).2.2 :=
        le_of_lt hvalidated.2.2.1
      have hbound :
          (shortLogPointAtOffset m ell samples offset).2.2.toNat < 2 ^ m := by
        rw [← Int.ofNat_lt]
        simpa [Int.toNat_of_nonneg hnonneg] using hvalidated.2.2.2.1
      simpa [hvalue] using hbound

/-- Quadratic factor recovery from a range-valid selected short logarithm
keeps every operand inside a linear public input envelope. -/
private theorem quadraticFactorRecoveryTrace_maxOperandWidth_le
    (N m ell shortLog : Nat) (hshortLog : shortLog < 2 ^ m) :
    NumberTheory.arithmeticEventListMaxOperandWidth
        (quadraticFactorRecoveryTrace N (some shortLog)).arithmetic ≤
      10 * shortLogRecoveryInputBits N m ell := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let center := shortLog + 1
  let centerSquare := center * center
  let discriminant := centerSquare - N
  let rootTrace := NumberTheory.integerSquareRootTrace discriminant
  let firstCandidate := center - rootTrace.value
  let secondCandidate := center + rootTrace.value
  let firstRemainder := N % firstCandidate
  let secondRemainder := N % secondCandidate
  let events :=
    (quadraticFactorRecoveryTrace N (some shortLog)).arithmetic
  have hinputBitsPos : 0 < inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hshortLogSize : Nat.size shortLog ≤ inputBits := by
    have hsize : Nat.size shortLog ≤ m := Nat.size_le.2 hshortLog
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hmodulusSize : Nat.size N ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hcenterSize : Nat.size center ≤ 2 * inputBits := by
    have h :=
      NumberTheory.natSize_add_le_max_add_one shortLog 1
    simp only [center]
    exact h.trans (by simp; omega)
  have hcenterSquareSize : Nat.size centerSquare ≤ 4 * inputBits := by
    exact
      (NumberTheory.natSize_mul_le_add center center).trans (by omega)
  have hdiscriminantSize : Nat.size discriminant ≤ 4 * inputBits := by
    exact
      (Nat.size_le_size (Nat.sub_le centerSquare N)).trans hcenterSquareSize
  have hrootSize : Nat.size rootTrace.value ≤ 4 * inputBits := by
    change Nat.size
        (NumberTheory.integerSquareRootTrace discriminant).value ≤
      4 * inputBits
    rw [NumberTheory.integerSquareRootTrace_value]
    exact
      (Nat.size_le_size (Nat.sqrt_le_self discriminant)).trans
        hdiscriminantSize
  have hfirstCandidateSize : Nat.size firstCandidate ≤ 4 * inputBits := by
    exact (Nat.size_le_size (Nat.sub_le center rootTrace.value)).trans
      (hcenterSize.trans (by omega))
  have hsecondCandidateSize : Nat.size secondCandidate ≤ 5 * inputBits := by
    exact
      (NumberTheory.natSize_add_le_max_add_one center rootTrace.value).trans
        (by omega)
  have hfirstRemainderSize : Nat.size firstRemainder ≤ inputBits := by
    exact (Nat.size_le_size (Nat.mod_le _ _)).trans hmodulusSize
  have hsecondRemainderSize : Nat.size secondRemainder ≤ inputBits := by
    exact (Nat.size_le_size (Nat.mod_le _ _)).trans hmodulusSize
  change NumberTheory.arithmeticEventListMaxOperandWidth events ≤
    10 * inputBits
  apply NumberTheory.arithmeticEventListMaxOperandWidth_le
  intro event hevent
  simp only [events, quadraticFactorRecoveryTrace, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hevent
  simp only [or_assoc] at hevent
  rcases hevent with h | h | h | h | h | h | h | h | h | h | h | h |
      h | h
  · subst event
    apply max_le
    · exact hshortLogSize.trans (by omega)
    · simp
      omega
  · subst event
    exact max_le (hcenterSize.trans (by omega))
      (hcenterSize.trans (by omega))
  · subst event
    exact max_le (hcenterSquareSize.trans (by omega))
      (hmodulusSize.trans (by omega))
  · exact
      (NumberTheory.ArithmeticEvent.operandWidth_le_listMax h).trans
        ((NumberTheory.integerSquareRootTrace_maxOperandWidth_le
          discriminant).trans (by
            calc
              2 * (Nat.size discriminant + 1) ≤
                  2 * (4 * inputBits + 1) :=
                Nat.mul_le_mul_left 2
                  (Nat.add_le_add_right hdiscriminantSize 1)
              _ ≤ 10 * inputBits := by omega))
  · subst event
    exact max_le (hcenterSize.trans (by omega))
      (by simpa [rootTrace, discriminant, centerSquare, center] using
        hrootSize.trans (by omega))
  · subst event
    exact max_le (hcenterSize.trans (by omega))
      (by simpa [rootTrace, discriminant, centerSquare, center] using
        hrootSize.trans (by omega))
  · subst event
    apply max_le
    · simp
      omega
    · simpa [firstCandidate, rootTrace, discriminant, centerSquare, center]
        using hfirstCandidateSize.trans (by omega)
  · subst event
    exact max_le
      (by simpa [firstCandidate, rootTrace, discriminant, centerSquare,
        center] using hfirstCandidateSize.trans (by omega))
      (hmodulusSize.trans (by omega))
  · subst event
    exact max_le (hmodulusSize.trans (by omega))
      (by simpa [firstCandidate, rootTrace, discriminant, centerSquare,
        center] using hfirstCandidateSize.trans (by omega))
  · subst event
    apply max_le
    · simpa [firstRemainder, firstCandidate, rootTrace, discriminant,
      centerSquare, center] using hfirstRemainderSize.trans (by omega)
    · simp
  · subst event
    apply max_le
    · simp
      omega
    · simpa [secondCandidate, rootTrace, discriminant, centerSquare, center]
        using hsecondCandidateSize.trans (by omega)
  · subst event
    exact max_le
      (by simpa [secondCandidate, rootTrace, discriminant, centerSquare,
        center] using hsecondCandidateSize.trans (by omega))
      (hmodulusSize.trans (by omega))
  · subst event
    exact max_le (hmodulusSize.trans (by omega))
      (by simpa [secondCandidate, rootTrace, discriminant, centerSquare,
        center] using hsecondCandidateSize.trans (by omega))
  · subst event
    apply max_le
    · simpa [secondRemainder, secondCandidate, rootTrace, discriminant,
      centerSquare, center] using hsecondRemainderSize.trans (by omega)
    · simp

/-- Quadratic factor recovery from any range-valid selected short logarithm
has cubic schoolbook charge in the same public input envelope. -/
private theorem quadraticFactorRecoveryTrace_schoolbookCharge_le
    (N m ell shortLog : Nat) (hshortLog : shortLog < 2 ^ m) :
    (quadraticFactorRecoveryTrace N (some shortLog)).schoolbookCharge ≤
      2 ^ 20 * shortLogRecoveryInputBits N m ell ^ 3 := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let center := shortLog + 1
  let centerSquare := center * center
  let discriminant := centerSquare - N
  let rootTrace := NumberTheory.integerSquareRootTrace discriminant
  let firstCandidate := center - rootTrace.value
  let secondCandidate := center + rootTrace.value
  let firstRemainder := N % firstCandidate
  let secondRemainder := N % secondCandidate
  let events :=
    (quadraticFactorRecoveryTrace N (some shortLog)).arithmetic
  have hinputBitsPos : 1 ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hshortLogSize : Nat.size shortLog ≤ inputBits := by
    have hsize : Nat.size shortLog ≤ m := Nat.size_le.2 hshortLog
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hmodulusSize : Nat.size N ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hcenterSize : Nat.size center ≤ 2 * inputBits := by
    have h :=
      NumberTheory.natSize_add_le_max_add_one shortLog 1
    simp only [center]
    exact h.trans (by simp; omega)
  have hcenterSquareSize : Nat.size centerSquare ≤ 4 * inputBits := by
    exact
      (NumberTheory.natSize_mul_le_add center center).trans (by omega)
  have hdiscriminantSize : Nat.size discriminant ≤ 4 * inputBits := by
    exact
      (Nat.size_le_size (Nat.sub_le centerSquare N)).trans hcenterSquareSize
  have hrootSize : Nat.size rootTrace.value ≤ 4 * inputBits := by
    change Nat.size
        (NumberTheory.integerSquareRootTrace discriminant).value ≤
      4 * inputBits
    rw [NumberTheory.integerSquareRootTrace_value]
    exact
      (Nat.size_le_size (Nat.sqrt_le_self discriminant)).trans
        hdiscriminantSize
  have hfirstCandidateSize : Nat.size firstCandidate ≤ 4 * inputBits := by
    exact (Nat.size_le_size (Nat.sub_le center rootTrace.value)).trans
      (hcenterSize.trans (by omega))
  have hsecondCandidateSize : Nat.size secondCandidate ≤ 5 * inputBits := by
    exact
      (NumberTheory.natSize_add_le_max_add_one center rootTrace.value).trans
        (by omega)
  have hfirstRemainderSize : Nat.size firstRemainder ≤ inputBits := by
    exact (Nat.size_le_size (Nat.mod_le _ _)).trans hmodulusSize
  have hsecondRemainderSize : Nat.size secondRemainder ≤ inputBits := by
    exact (Nat.size_le_size (Nat.mod_le _ _)).trans hmodulusSize
  have hlength : events.length ≤ 32 * inputBits := by
    have hrounds :
        NumberTheory.integerSquareRootRounds discriminant ≤
          Nat.size discriminant := by
      simp only [NumberTheory.integerSquareRootRounds]
      omega
    have hexact :
        events.length =
          16 + 4 * NumberTheory.integerSquareRootRounds discriminant := by
      simp [events, quadraticFactorRecoveryTrace,
        NumberTheory.integerSquareRootTrace_arithmetic_length]
      ring
    rw [hexact]
    omega
  have hwidth :
      NumberTheory.arithmeticEventListMaxOperandWidth events ≤
        10 * inputBits := by
    apply NumberTheory.arithmeticEventListMaxOperandWidth_le
    intro event hevent
    simp only [events, quadraticFactorRecoveryTrace, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hevent
    simp only [or_assoc] at hevent
    rcases hevent with h | h | h | h | h | h | h | h | h | h | h | h |
        h | h
    · subst event
      apply max_le
      · exact hshortLogSize.trans (by omega)
      · simp
        omega
    · subst event
      exact max_le (hcenterSize.trans (by omega))
        (hcenterSize.trans (by omega))
    · subst event
      exact max_le (hcenterSquareSize.trans (by omega))
        (hmodulusSize.trans (by omega))
    · exact
        (NumberTheory.ArithmeticEvent.operandWidth_le_listMax h).trans
          ((NumberTheory.integerSquareRootTrace_maxOperandWidth_le
            discriminant).trans (by omega))
    · subst event
      exact max_le (hcenterSize.trans (by omega))
        (by simpa [rootTrace, discriminant, centerSquare, center] using
          hrootSize.trans (by omega))
    · subst event
      exact max_le (hcenterSize.trans (by omega))
        (by simpa [rootTrace, discriminant, centerSquare, center] using
          hrootSize.trans (by omega))
    · subst event
      apply max_le
      · simp
        omega
      · simpa [firstCandidate, rootTrace, discriminant, centerSquare, center]
          using hfirstCandidateSize.trans (by omega)
    · subst event
      exact max_le
        (by simpa [firstCandidate, rootTrace, discriminant, centerSquare,
          center] using hfirstCandidateSize.trans (by omega))
        (hmodulusSize.trans (by omega))
    · subst event
      exact max_le (hmodulusSize.trans (by omega))
        (by simpa [firstCandidate, rootTrace, discriminant, centerSquare,
          center] using hfirstCandidateSize.trans (by omega))
    · subst event
      apply max_le
      · simpa [firstRemainder, firstCandidate, rootTrace, discriminant,
          centerSquare, center] using hfirstRemainderSize.trans (by omega)
      · simp
    · subst event
      apply max_le
      · simp
        omega
      · simpa [secondCandidate, rootTrace, discriminant, centerSquare, center]
          using hsecondCandidateSize.trans (by omega)
    · subst event
      exact max_le
        (by simpa [secondCandidate, rootTrace, discriminant, centerSquare,
          center] using hsecondCandidateSize.trans (by omega))
        (hmodulusSize.trans (by omega))
    · subst event
      exact max_le (hmodulusSize.trans (by omega))
        (by simpa [secondCandidate, rootTrace, discriminant, centerSquare,
          center] using hsecondCandidateSize.trans (by omega))
    · subst event
      apply max_le
      · simpa [secondRemainder, secondCandidate, rootTrace, discriminant,
          centerSquare, center] using hsecondRemainderSize.trans (by omega)
      · simp
  have hopen : 10 * inputBits + 1 ≤ 11 * inputBits := by omega
  have hsquare :
      (10 * inputBits + 1) ^ 2 ≤ (11 * inputBits) ^ 2 :=
    Nat.pow_le_pow_left hopen 2
  calc
    (quadraticFactorRecoveryTrace N (some shortLog)).schoolbookCharge =
        NumberTheory.arithmeticEventListCharge events := by
      rfl
    _ ≤ 4 * events.length *
        (NumberTheory.arithmeticEventListMaxOperandWidth events + 1) ^ 2 :=
      NumberTheory.arithmeticEventListCharge_le events
    _ ≤ 4 * (32 * inputBits) * (10 * inputBits + 1) ^ 2 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 hlength)
        (Nat.pow_le_pow_left (Nat.add_le_add_right hwidth 1) 2)
    _ ≤ 4 * (32 * inputBits) * (11 * inputBits) ^ 2 :=
      Nat.mul_le_mul_left (4 * (32 * inputBits)) hsquare
    _ = (4 * 32 * 11 ^ 2) * inputBits ^ 3 := by ring
    _ ≤ 2 ^ 20 * inputBits ^ 3 :=
      Nat.mul_le_mul_right _ (by norm_num)

/-- The complete two-sample Ekerå–Håstad recovery, including its fixed
coefficient scan and factor extraction, has a uniform cubic schoolbook-charge
bound in the public input bit envelope. -/
theorem shortLogPairRecoveryTrace_schoolbookCharge_le
    {N : Nat} (m ell : Nat) (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (hN : 0 < N) :
    (shortLogPairRecoveryTrace m ell generator samples).schoolbookCharge ≤
      2 ^ 80 * shortLogRecoveryInputBits N m ell ^ 3 := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let trace := shortLogPairRecoveryTrace m ell generator samples
  have hinputBitsPos : 1 ≤ inputBits := by
    dsimp only [inputBits, shortLogRecoveryInputBits]
    omega
  have hspec := shortLogPairRecoveryTrace_spec m ell generator samples
  have hsetup :
      NumberTheory.arithmeticEventListCharge trace.setup.arithmetic ≤
        2 ^ 16 * inputBits ^ 3 := by
    rw [hspec.setup_eq]
    simpa [inputBits] using
      shortLogPairSetupTrace_schoolbookCharge_le
        (N := N) m ell samples
  have hreduction :
      trace.reduction.schoolbookCharge ≤ 2 ^ 29 * inputBits ^ 3 := by
    rw [hspec.reduction_eq]
    have h := shortLogRecoveryTrace_schoolbookCharge_le m ell samples
    have hbits : ell + m + 1 ≤ inputBits := by
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega
    calc
      (shortLogRecoveryTrace m ell samples).schoolbookCharge ≤
          295_276_800 * (ell + m + 1) ^ 3 := h
      _ ≤ 295_276_800 * inputBits ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbits 3)
      _ ≤ 2 ^ 29 * inputBits ^ 3 :=
        Nat.mul_le_mul_right _ (by norm_num)
  have hnearest :
      trace.nearest.schoolbookCharge ≤ 2 ^ 31 * inputBits ^ 3 := by
    rw [hspec.nearest_eq, hspec.reduction_eq]
    simpa [inputBits] using
      shortLogNearestPlaneTrace_schoolbookCharge_le N m ell samples
  have htarget :
      trace.targetPower.schoolbookCharge ≤ 2 ^ 11 * inputBits ^ 3 := by
    rw [hspec.targetPower_eq]
    have hraw :=
      NumberTheory.modularPowerTrace_schoolbookCharge_cubic generator.val hN
        (Nat.lt_size_self (targetExponent N))
    have henvelope :
        Nat.size N + Nat.size (targetExponent N) + 1 ≤ 2 * inputBits := by
      have htargetSize := targetExponent_size_le N
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega
    calc
      (NumberTheory.modularPowerTrace (Nat.size (targetExponent N))
          generator.val (targetExponent N)).schoolbookCharge ≤
          252 * (Nat.size N + Nat.size (targetExponent N) + 1) ^ 3 := hraw
      _ ≤ 252 * (2 * inputBits) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left henvelope 3)
      _ = 2016 * inputBits ^ 3 := by ring
      _ ≤ 2 ^ 11 * inputBits ^ 3 :=
        Nat.mul_le_mul_right _ (by norm_num)
  have hselector :
      trace.selector.schoolbookCharge ≤ 2 ^ 74 * inputBits ^ 3 := by
    simpa [trace, inputBits] using
      shortLogPairRecoveryTrace_selector_charge_le
        m ell generator samples hN
  have hquadratic :
      trace.quadratic.trace.schoolbookCharge ≤ 2 ^ 20 * inputBits ^ 3 := by
    rw [trace.quadratic.canonical]
    cases hselected : trace.selector.selected with
    | none =>
        simp [quadraticFactorRecoveryTrace,
          QuadraticFactorRecoveryTrace.schoolbookCharge,
          NumberTheory.arithmeticEventListCharge]
    | some shortLog =>
        have hshortLog :
            shortLog < 2 ^ m := by
          exact shortLogPairRecoveryTrace_selected_lt generator samples
            (by simpa [trace] using hselected)
        simpa [inputBits] using
          quadraticFactorRecoveryTrace_schoolbookCharge_le
            N m ell shortLog hshortLog
  rw [ShortLogPairRecoveryTrace.schoolbookCharge_eq]
  calc
    NumberTheory.arithmeticEventListCharge trace.setup.arithmetic +
        trace.reduction.schoolbookCharge + trace.nearest.schoolbookCharge +
        trace.targetPower.schoolbookCharge + trace.selector.schoolbookCharge +
        trace.quadratic.trace.schoolbookCharge ≤
        2 ^ 16 * inputBits ^ 3 + 2 ^ 29 * inputBits ^ 3 +
        2 ^ 31 * inputBits ^ 3 +
        2 ^ 11 * inputBits ^ 3 + 2 ^ 74 * inputBits ^ 3 +
        2 ^ 20 * inputBits ^ 3 := by omega
    _ = (2 ^ 16 + 2 ^ 29 + 2 ^ 31 + 2 ^ 11 + 2 ^ 74 + 2 ^ 20) *
        inputBits ^ 3 := by ring
    _ ≤ 2 ^ 80 * inputBits ^ 3 :=
      Nat.mul_le_mul_right _ (by norm_num)

/-- Every arithmetic operand in one sealed two-sample Ekerå–Håstad recovery
fits the fixed public short-log input envelope. -/
theorem shortLogPairRecoveryTrace_maxOperandWidth_le
    {N : Nat} (m ell : Nat) (generator : (ZMod N)ˣ)
    (samples : ShortLogSample m ell × ShortLogSample m ell)
    (hN : 0 < N) :
    (shortLogPairRecoveryTrace m ell generator samples).maxOperandWidth ≤
      2 ^ 20 * shortLogRecoveryInputBits N m ell := by
  let inputBits := shortLogRecoveryInputBits N m ell
  let trace := shortLogPairRecoveryTrace m ell generator samples
  have hspec := shortLogPairRecoveryTrace_spec m ell generator samples
  have hsetup :
      NumberTheory.arithmeticEventListMaxOperandWidth trace.setup.arithmetic ≤
        2 ^ 20 * inputBits := by
    rw [hspec.setup_eq]
    calc
      NumberTheory.arithmeticEventListMaxOperandWidth
          (shortLogPairSetupTrace (N := N) m ell samples).arithmetic ≤
          16 * inputBits := by
        simpa [inputBits] using
          shortLogPairSetupTrace_maxOperandWidth_le (N := N) m ell samples
      _ ≤ 2 ^ 20 * inputBits :=
        Nat.mul_le_mul_right _ (by norm_num)
  have hreduction :
      NumberTheory.arithmeticEventListMaxOperandWidth trace.reduction.arithmetic ≤
        2 ^ 20 * inputBits := by
    rw [hspec.reduction_eq]
    calc
      NumberTheory.arithmeticEventListMaxOperandWidth
          (shortLogRecoveryTrace m ell samples).arithmetic ≤
          256 * inputBits := by
        simpa [NumberTheory.LatticeReductionTrace3.maxOperandWidth, inputBits]
          using shortLogRecoveryTrace_maxOperandWidth_le N m ell samples
      _ ≤ 2 ^ 20 * inputBits :=
        Nat.mul_le_mul_right _ (by norm_num)
  have hnearest :
      NumberTheory.arithmeticEventListMaxOperandWidth trace.nearest.arithmetic ≤
        2 ^ 20 * inputBits := by
    rw [hspec.nearest_eq, hspec.reduction_eq]
    calc
      NumberTheory.arithmeticEventListMaxOperandWidth
          (NumberTheory.nearestPlaneTrace3
            (shortLogRecoveryTrace m ell samples).output
            (shortLogLatticeTarget m ell samples)).arithmetic ≤
          256 * inputBits := by
        simpa [NumberTheory.NearestPlaneTrace3.maxOperandWidth, inputBits]
          using shortLogNearestPlaneTrace_maxOperandWidth_le N m ell samples
      _ ≤ 2 ^ 20 * inputBits :=
        Nat.mul_le_mul_right _ (by norm_num)
  have htarget :
      NumberTheory.arithmeticEventListMaxOperandWidth trace.targetPower.arithmetic ≤
        2 ^ 20 * inputBits := by
    rw [hspec.targetPower_eq]
    have hraw :=
      NumberTheory.modularPowerTrace_maxOperandWidth_le generator.val hN
        (Nat.lt_size_self (targetExponent N))
    have henvelope :
        Nat.size N + Nat.size (targetExponent N) + 1 ≤ 2 * inputBits := by
      have htargetSize := targetExponent_size_le N
      dsimp only [inputBits, shortLogRecoveryInputBits]
      omega
    calc
      NumberTheory.arithmeticEventListMaxOperandWidth
          (NumberTheory.modularPowerTrace (Nat.size (targetExponent N))
            generator.val (targetExponent N)).arithmetic ≤
          2 * (Nat.size N + Nat.size (targetExponent N) + 1) := hraw
      _ ≤ 2 * (2 * inputBits) :=
        Nat.mul_le_mul_left 2 henvelope
      _ = 4 * inputBits := by ring
      _ ≤ 2 ^ 20 * inputBits :=
        Nat.mul_le_mul_right _ (by norm_num)
  have hselector :
      NumberTheory.arithmeticEventListMaxOperandWidth trace.selector.arithmetic ≤
        2 ^ 20 * inputBits := by
    simpa [trace, inputBits] using
      shortLogPairRecoveryTrace_selector_maxOperandWidth_le
        m ell generator samples hN
  have hquadratic :
      NumberTheory.arithmeticEventListMaxOperandWidth
          trace.quadratic.trace.arithmetic ≤
        2 ^ 20 * inputBits := by
    rw [trace.quadratic.canonical]
    cases hselected : trace.selector.selected with
    | none =>
        simp [quadraticFactorRecoveryTrace,
          NumberTheory.arithmeticEventListMaxOperandWidth]
    | some shortLog =>
        have hshortLog : shortLog < 2 ^ m := by
          exact shortLogPairRecoveryTrace_selected_lt generator samples
            (by simpa [trace] using hselected)
        calc
          NumberTheory.arithmeticEventListMaxOperandWidth
              (quadraticFactorRecoveryTrace N (some shortLog)).arithmetic ≤
              10 * inputBits := by
            simpa [inputBits] using
              quadraticFactorRecoveryTrace_maxOperandWidth_le
                N m ell shortLog hshortLog
          _ ≤ 2 ^ 20 * inputBits :=
            Nat.mul_le_mul_right _ (by norm_num)
  change NumberTheory.arithmeticEventListMaxOperandWidth
      (trace.setup.arithmetic ++ trace.reduction.arithmetic ++
        trace.nearest.arithmetic ++ trace.targetPower.arithmetic ++
          trace.selector.arithmetic ++ trace.quadratic.trace.arithmetic) ≤
        2 ^ 20 * inputBits
  simp only [NumberTheory.arithmeticEventListMaxOperandWidth_append]
  exact max_le (max_le (max_le (max_le (max_le hsetup hreduction) hnearest)
    htarget) hselector) hquadratic

/-- A valid short-log candidate is exactly what the closed selector returns
whenever the target relation is injective throughout the advertised range. -/
theorem recoverShortLogFromPair_eq_some_of_candidate
    {N m ell secret : Nat} {generator : (ZMod N)ˣ}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hfeasible : ShortLogRecoveryFeasible m ell samples)
    (horder : 2 ^ m ≤ orderOf generator)
    (hcandidate : ShortLogPairCandidate m ell generator samples secret) :
    recoverShortLogFromPair m ell generator samples = some secret := by
  have hsecretMem : secret ∈ shortLogCandidateList m ell generator samples :=
    shortLogCandidate_mem hfeasible hcandidate
  let candidateList := shortLogCandidateList m ell generator samples
  have hlistNonempty : candidateList ≠ [] :=
    List.ne_nil_of_mem (by simpa [candidateList] using hsecretMem)
  let selected := candidateList.head hlistNonempty
  have hselectedMem : selected ∈ candidateList :=
    List.head_mem hlistNonempty
  rcases shortLogCandidateList_member_validated
      (by simpa [candidateList] using hselectedMem) with
    ⟨offset, _hresult, hvalidated, hselectedValue⟩
  have hpointValue := ShortLogValidatedPoint.toNat_eq_candidate
    horder hcandidate hvalidated
  have hselected : selected = secret := hselectedValue.symm.trans hpointValue
  calc
    recoverShortLogFromPair m ell generator samples =
        (shortLogPairRecoveryTrace m ell generator samples).selector.selected :=
      recoverShortLogFromPair_eq_selector m ell generator samples
    _ = (shortLogCandidateList m ell generator samples).head? :=
      shortLogPairRecoveryTrace_selected m ell generator samples
    _ = candidateList.head? := by rfl
    _ = some selected := by rw [List.head?_eq_some_head hlistNonempty]
    _ = some secret := congrArg some hselected

/-- For distinct odd primes, the public exponent produces the RSA short
logarithm in every cyclic subgroup generated by a unit.  This is the actual
reduction used by the short-DLP circuit, not a caller-supplied relation
[EH17, source.tex:915-925]. -/
theorem targetUnit_eq_shortLog {p q : Nat}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpOdd : Odd p) (hqOdd : Odd q)
    (generator : (ZMod (p * q))ˣ) :
    targetUnit generator = generator ^ shortLogSecret p q := by
  have hcoprime : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  have hpTwo : p ≠ 2 := by
    intro h
    subst p
    rcases hpOdd with ⟨k, hk⟩
    omega
  have hqTwo : q ≠ 2 := by
    intro h
    subst q
    rcases hqOdd with ⟨k, hk⟩
    omega
  have hcp : ArithmeticFunction.carmichael p = p - 1 := by
    simpa [Nat.totient_prime hp] using
      (ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hp hpTwo)
  have hcq : ArithmeticFunction.carmichael q = q - 1 := by
    simpa [Nat.totient_prime hq] using
      (ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hq hqTwo)
  rcases hpOdd with ⟨a, ha⟩
  rcases hqOdd with ⟨b, hb⟩
  have hcarm :
      ArithmeticFunction.carmichael (p * q) ∣
        ((p - 1) * (q - 1)) / 2 := by
    rw [ArithmeticFunction.carmichael_mul hcoprime, hcp, hcq, ha, hb]
    rw [show 2 * a + 1 - 1 = 2 * a by omega,
      show 2 * b + 1 - 1 = 2 * b by omega,
      Nat.lcm_mul_left]
    have hright : 2 * a * (2 * b) / 2 = 2 * (a * b) := by
      rw [show 2 * a * (2 * b) = 2 * (2 * (a * b)) by ring,
        mul_comm 2 (2 * (a * b)),
        Nat.mul_div_left _ (by norm_num : 0 < 2)]
    rw [hright]
    exact Nat.mul_dvd_mul_left 2 (Nat.lcm_dvd_mul a b)
  have hpowHalf : generator ^ (((p - 1) * (q - 1)) / 2) = 1 := by
    rcases hcarm with ⟨k, hk⟩
    rw [hk, pow_mul, ArithmeticFunction.pow_carmichael, one_pow]
  have hexponent :
      targetExponent (p * q) =
        shortLogSecret p q + ((p - 1) * (q - 1)) / 2 := by
    rw [ha, hb]
    have htarget :
        (((2 * a + 1) * (2 * b + 1) - 1) / 2) =
          a + b + 2 * (a * b) := by
      have hprod :
          (2 * a + 1) * (2 * b + 1) =
            2 * (a + b + 2 * (a * b)) + 1 := by ring
      rw [hprod, Nat.add_sub_cancel,
        mul_comm 2 (a + b + 2 * (a * b)),
        Nat.mul_div_left _ (by norm_num : 0 < 2)]
    have hshort :
        ((2 * a + 1 + (2 * b + 1) - 2) / 2) = a + b := by
      omega
    have hhalf :
        (((2 * a + 1 - 1) * (2 * b + 1 - 1)) / 2) =
          2 * (a * b) := by
      rw [show 2 * a + 1 - 1 = 2 * a by omega,
        show 2 * b + 1 - 1 = 2 * b by omega,
        show 2 * a * (2 * b) = 2 * (2 * (a * b)) by ring,
        mul_comm 2 (2 * (a * b)),
        Nat.mul_div_left _ (by norm_num : 0 < 2)]
    unfold targetExponent shortLogSecret
    rw [htarget, hshort, hhalf]
  rw [targetUnit, hexponent, pow_add, hpowHalf, mul_one]

/-- For ordered odd factors, the quadratic constructed from the hidden short
logarithm has the original factors as its two roots. -/
theorem quadraticFactorCandidates_shortLogSecret_of_le
    {p q : Nat} (hpOdd : Odd p) (hqOdd : Odd q) (hpq : p ≤ q) :
    quadraticFactorCandidates (p * q) (shortLogSecret p q) = (p, q) := by
  rcases hpOdd with ⟨a, rfl⟩
  rcases hqOdd with ⟨b, rfl⟩
  have hab : a ≤ b := by omega
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  have hshort :
      shortLogSecret (2 * a + 1) (2 * (a + c) + 1) = 2 * a + c := by
    unfold shortLogSecret
    omega
  have hdisc :
      quadraticDiscriminant ((2 * a + 1) * (2 * (a + c) + 1))
          (shortLogSecret (2 * a + 1) (2 * (a + c) + 1)) = c ^ 2 := by
    unfold quadraticDiscriminant quadraticCenter
    rw [hshort]
    have hsquare :
        (2 * a + c + 1) ^ 2 =
          (2 * a + 1) * (2 * (a + c) + 1) + c ^ 2 := by
      ring
    rw [hsquare, Nat.add_sub_cancel_left]
  rw [quadraticFactorCandidates_eq, hshort]
  have hdisc' :
      quadraticDiscriminant ((2 * a + 1) * (2 * (a + c) + 1))
          (2 * a + c) = c ^ 2 := by
    rw [← hshort]
    exact hdisc
  rw [hdisc', Nat.sqrt_eq']
  apply Prod.ext
  · unfold quadraticCenter
    omega
  · unfold quadraticCenter
    omega

/-- On ordered distinct odd primes, the closed quadratic selector returns the
smaller declared factor. -/
theorem recoverFactorFromShortLog_shortLogSecret_of_le
    {p q : Nat} (hp : p.Prime) (hq : q.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hpq : p ≤ q) :
    recoverFactorFromShortLog (p * q) (shortLogSecret p q) = some p := by
  have hpN : p < p * q :=
    lt_mul_of_one_lt_right hp.pos hq.one_lt
  have hroots :=
    quadraticFactorCandidates_shortLogSecret_of_le hpOdd hqOdd hpq
  rw [quadraticFactorCandidates_eq] at hroots
  have hfirst :
      quadraticCenter (shortLogSecret p q) -
          Nat.sqrt (quadraticDiscriminant (p * q) (shortLogSecret p q)) = p :=
    congrArg Prod.fst hroots
  have hsecond :
      quadraticCenter (shortLogSecret p q) +
          Nat.sqrt (quadraticDiscriminant (p * q) (shortLogSecret p q)) = q :=
    congrArg Prod.snd hroots
  rw [recoverFactorFromShortLog_eq, hfirst, hsecond]
  simp [hp.one_lt, hpN]

/-- For distinct odd primes in either order, quadratic recovery returns one of
the two declared factors. -/
theorem recoverFactorFromShortLog_shortLogSecret
    {p q : Nat} (hp : p.Prime) (hq : q.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) :
    recoverFactorFromShortLog (p * q) (shortLogSecret p q) = some p ∨
      recoverFactorFromShortLog (p * q) (shortLogSecret p q) = some q := by
  rcases le_total p q with hpq | hqp
  · exact Or.inl
      (recoverFactorFromShortLog_shortLogSecret_of_le
        hp hq hpOdd hqOdd hpq)
  · right
    simpa [mul_comm, shortLogSecret, add_comm] using
      (recoverFactorFromShortLog_shortLogSecret_of_le
        hq hp hqOdd hpOdd hqp)

/-- A valid narrow-good pair at the true short logarithm reaches one of the
two declared RSA factors through the complete closed recovery composition. -/
theorem recoverFactorFromShortLogPair_shortLogSecret
    {p q m ell : Nat} {generator : (ZMod (p * q))ˣ}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hp : p.Prime) (hq : q.Prime) (hpOdd : Odd p) (hqOdd : Odd q)
    (hfeasible : ShortLogRecoveryFeasible m ell samples)
    (horder : 2 ^ m ≤ orderOf generator)
    (hcandidate : ShortLogPairCandidate m ell generator samples
      (shortLogSecret p q)) :
    recoverFactorFromShortLogPair m ell generator samples = some p ∨
      recoverFactorFromShortLogPair m ell generator samples = some q := by
  have hshort :=
    recoverShortLogFromPair_eq_some_of_candidate hfeasible horder hcandidate
  have hpair :
      recoverFactorFromShortLogPair m ell generator samples =
        recoverFactorFromShortLog (p * q) (shortLogSecret p q) := by
    calc
      recoverFactorFromShortLogPair m ell generator samples =
          (quadraticFactorRecoveryTrace (p * q)
            (recoverShortLogFromPair m ell generator samples)).result :=
        recoverFactorFromShortLogPair_eq_run m ell generator samples
      _ = (quadraticFactorRecoveryTrace (p * q)
          (some (shortLogSecret p q))).result := by rw [hshort]
      _ = recoverFactorFromShortLog (p * q) (shortLogSecret p q) := by rfl
  rw [hpair]
  exact recoverFactorFromShortLog_shortLogSecret hp hq hpOdd hqOdd

/-- Quadratic recovery never returns a spurious or trivial divisor. -/
theorem recoverFactorFromShortLog_some_sound {N shortLog factor : Nat}
    (hresult : recoverFactorFromShortLog N shortLog = some factor) :
    factor ∣ N ∧ 1 < factor ∧ factor < N := by
  rw [recoverFactorFromShortLog_eq] at hresult
  dsimp only at hresult
  split at hresult
  next hfirstValid =>
    rcases hfirstValid with ⟨hfirstPos, hfirstLt, hfirstMod⟩
    simp only [Option.some.injEq] at hresult
    subst factor
    exact ⟨Nat.dvd_of_mod_eq_zero hfirstMod, hfirstPos, hfirstLt⟩
  next _hfirstInvalid =>
    split at hresult
    next hsecondValid =>
      rcases hsecondValid with ⟨hsecondPos, hsecondLt, hsecondMod⟩
      simp only [Option.some.injEq] at hresult
      subst factor
      exact ⟨Nat.dvd_of_mod_eq_zero hsecondMod, hsecondPos, hsecondLt⟩
    next _hsecondInvalid => contradiction

/-- Two-sample recovery never emits a spurious or trivial divisor. -/
theorem recoverFactorFromShortLogPair_some_sound
    {N m ell factor : Nat} {generator : (ZMod N)ˣ}
    {samples : ShortLogSample m ell × ShortLogSample m ell}
    (hresult : recoverFactorFromShortLogPair m ell generator samples =
      some factor) :
    factor ∣ N ∧ 1 < factor ∧ factor < N := by
  rw [recoverFactorFromShortLogPair_eq_run] at hresult
  cases hselector : recoverShortLogFromPair m ell generator samples with
  | none =>
      rw [hselector] at hresult
      simp [quadraticFactorRecoveryTrace] at hresult
  | some shortLog =>
      exact recoverFactorFromShortLog_some_sound (by
        change (quadraticFactorRecoveryTrace N (some shortLog)).result =
          some factor
        simpa only [hselector] using hresult)

end ExecutableShortLogRecovery

end RSA
end QuantumAlg

end
