/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.PairedExponents
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Output.Coordinates

/-!
# The literal native preparation and Fourier coefficients of a streaming path

 The original
native inverse Fourier row is evaluated at the actual path frequency, whose
per-block bit reversal is a mathematical output coordinate. The range
preparation retains all padded zero amplitudes. Only complex scalars change
order; no arithmetic matrix or measured path sum changes order here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Fourier
namespace Coefficients

noncomputable section

open QuantumAlg QuantumAlg.QuantumFourierTransform QuantumFourierTransform.Semiclassical
open QuantumAlg.FiniteCyclicDLP
open Recovery.Stage.PointCoordinates
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity
open ActualFeedback

/-- Real and complex inverse square roots coincide, including range size zero. -/
lemma invSqrtOrder_real (count : Nat) :
    OrderPreparation.invSqrtOrder count = (invSqrt count : ℂ) := by
  simp only [OrderPreparation.invSqrtOrder, invSqrt, Complex.ofReal_inv]

/-- A literal native inverse-QFT row is the complete-source partner row. -/
lemma native_inverse_fullRow (m : Nat) (frequency : Fin (2 ^ m)) (input : Bits m) :
    star (QFTOperator m) frequency (binaryEquiv m input) =
      Partner.fullRows true m frequency input := by
  simp only [Partner.fullRows, ↓reduceIte, Native.qftNative_inverseCircuit_binaryMatrix]

/-- The actual chronological output chooses the same literal native row coefficient. -/
lemma native_inverse_pathRow (width m : Nat)
    (path : Fin (2 * m) → Branch width m) (second : Bool) (input : Bits m) :
    star (QFTOperator m) (ActualFeedback.blockFrequency width m path second)
        (binaryEquiv m input) =
      Partner.fourierRows true m (blockOutput width m path second) input := by
  rw [native_inverse_fullRow, ActualFeedback.blockFrequency_fullRow]

universe u
variable {G : Type u} [Group G]

/-- Both native ranges keep their exact amplitudes at every original finite input label. -/
lemma preparation_tuple_real (problem : KnownOrderProblem G)
    (first second : Bits (orderWidth problem)) :
    Recovery.Reference.Exponents.preparationAmplitude problem
        (Recovery.Fourier.PairedExponents.tuplePair (orderWidth problem) (first, second)) =
      ((if (binaryEquiv (orderWidth problem) first).val < problem.order then
          invSqrt problem.order else 0 : ℝ) : ℂ) *
        ((if (binaryEquiv (orderWidth problem) second).val < problem.order then
          invSqrt problem.order else 0 : ℝ) : ℂ) := by
  rw [Recovery.Fourier.PairedExponents.preparation_tuple_amplitude]
  by_cases firstInside : (binaryEquiv (orderWidth problem) first).val < problem.order
  · by_cases secondInside : (binaryEquiv (orderWidth problem) second).val < problem.order
    · simp only [if_pos firstInside, if_pos secondInside, invSqrtOrder_real]
    · simp only [if_pos firstInside, if_neg secondInside, Complex.ofReal_zero, mul_zero]
  · simp only [if_neg firstInside, Complex.ofReal_zero, zero_mul]

/-- The original paired inverse Fourier readout has exactly the two actual physical rows. -/
lemma readout_tuple_rows (problem : KnownOrderProblem G) (width : Nat)
    (path : Fin (2 * orderWidth problem) → Branch width (orderWidth problem))
    (first second : Bits (orderWidth problem)) :
    Recovery.Reference.Exponents.readoutCoefficient problem
        (ActualFeedback.pathFrequency width (orderWidth problem) path)
        (Recovery.Fourier.PairedExponents.tuplePair (orderWidth problem) (first, second)) =
      Partner.fourierRows true (orderWidth problem)
          (blockOutput width (orderWidth problem) path false) first *
        Partner.fourierRows true (orderWidth problem)
          (blockOutput width (orderWidth problem) path true) second := by
  change star (QFTOperator (orderWidth problem))
        (ActualFeedback.blockFrequency width (orderWidth problem) path false)
        (binaryEquiv (orderWidth problem) first) *
      star (QFTOperator (orderWidth problem))
        (ActualFeedback.blockFrequency width (orderWidth problem) path true)
        (binaryEquiv (orderWidth problem) second) = _
  rw [native_inverse_pathRow, native_inverse_pathRow]

/-- Native contraction coefficients equal the exact streaming double-sum coefficients. -/
lemma native_streaming_coefficient (problem : KnownOrderProblem G) (width : Nat)
    (path : Fin (2 * orderWidth problem) → Branch width (orderWidth problem))
    (first second : Bits (orderWidth problem)) :
    Recovery.Reference.Exponents.preparationAmplitude problem
          (Recovery.Fourier.PairedExponents.tuplePair (orderWidth problem) (first, second)) *
        Recovery.Reference.Exponents.readoutCoefficient problem
          (ActualFeedback.pathFrequency width (orderWidth problem) path)
          (Recovery.Fourier.PairedExponents.tuplePair (orderWidth problem) (first, second)) =
      (((if (binaryEquiv (orderWidth problem) second).val < problem.order then
            invSqrt problem.order else 0 : ℝ) : ℂ) *
          ((if (binaryEquiv (orderWidth problem) first).val < problem.order then
            invSqrt problem.order else 0 : ℝ) : ℂ)) *
        (Partner.fourierRows true (orderWidth problem)
            (blockOutput width (orderWidth problem) path true) second *
          Partner.fourierRows true (orderWidth problem)
            (blockOutput width (orderWidth problem) path false) first) := by
  rw [preparation_tuple_real, readout_tuple_rows]
  ac_rfl

end

end Coefficients
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Fourier
