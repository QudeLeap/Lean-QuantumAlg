/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.ScalarRows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.ActualFeedback
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.WordRecursion
import all QuantumAlg.Util.FinPow.BinaryBasis
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-!
# Actual within-block feedback gives the negative physical Fourier row

The complete two-block guard is restricted using the existing chronological block index.
The output tuple is derived from the actual measured path, not assumed as an extra
semantic certificate. Only complex scalar factors are rearranged.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.PathDensity
namespace ActualFeedback

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open Recovery.Stage.PointCoordinates
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Existing blockIndex, read in chronological rather than remaining-width order. -/
abbrev position {m : Nat} (second : Bool) (current : Fin m) : Fin (2 * m) :=
  blockIndex second current.rev

private lemma position_val {m : Nat} (second : Bool) (current : Fin m) :
    (position second current).val = if second then m + current.val else current.val := by
  refine (congrArg (fun index : Fin (2 * m) => index.val)
    (blockIndex_original_order second current)).trans ?_
  cases second <;> rfl

private lemma position_block {m : Nat} (second : Bool) (current : Fin m) :
    (position second current).val / m = if second then 1 else 0 := by
  rw [position_val]
  cases second with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact Nat.div_eq_of_lt current.isLt
  | true =>
      have positive : 0 < m := lt_of_le_of_lt (Nat.zero_le current.val) current.isLt
      simp only [↓reduceIte]
      rw [Nat.add_div_left current.val positive, Nat.div_eq_of_lt current.isLt]

private lemma feeds_same {m : Nat} (second : Bool) (previous current : Fin m) :
    Recovery.Layout.feeds m (position second previous) (position second current) ↔
      previous.val < current.val := by
  unfold Recovery.Layout.feeds
  rw [position_block, position_block]
  simp only [and_true]
  rw [position_val, position_val]
  cases second <;> simp

private lemma feeds_other {m : Nat} (second : Bool) (previous current : Fin m) :
    ¬ Recovery.Layout.feeds m (position (!second) previous) (position second current) := by
  unfold Recovery.Layout.feeds
  rw [position_block, position_block]
  cases second <;> simp

private lemma position_distance {m : Nat} (second : Bool) (previous current : Fin m) :
    (position second current).val - (position second previous).val - 1 =
      current.val - previous.val - 1 := by
  rw [position_val, position_val]
  cases second <;> simp only [Bool.false_eq_true, ↓reduceIte]
  omega

private lemma factor_same {m : Nat} (bits : Fin (2 * m) → Fin 2)
    (second : Bool) (output : Bits m)
    (coordinates : ∀ current, bits (position second current) = tupleCoordinates m output current)
    (previous current : Fin m) (bit : Fin 2) :
    recordFactor m bits (position second current) (position second previous) bit =
      if bit = 0 then 1 else
        if previous.val < current.val ∧ tupleCoordinates m output previous = 1 then
          Partner.rotation true (current.val - previous.val - 1)
        else 1 := by
  simp only [recordFactor, feeds_same, coordinates, position_distance]
  by_cases zero : bit = 0 <;>
    by_cases earlier : previous.val < current.val <;>
    by_cases selected : tupleCoordinates m output previous = 1 <;>
    simp [zero, earlier, selected]

private lemma factor_other {m : Nat} (bits : Fin (2 * m) → Fin 2)
    (second : Bool) (previous current : Fin m) (bit : Fin 2) :
    recordFactor m bits (position second current) (position (!second) previous) bit = 1 := by
  exact if_neg (feeds_other second previous current)

private lemma split_blocks {m : Nat} (factor : Fin (2 * m) → ℂ) :
    (∏ previous : Fin (2 * m), factor previous) =
      (∏ previous : Fin m, factor (position false previous)) *
        ∏ previous : Fin m, factor (position true previous) := by
  rw [← (finCongr (Nat.two_mul m).symm).prod_comp factor, Fin.prod_univ_add]
  simp only [position, blockIndex_original_order, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- No contribution is taken from the other exponent block. -/
lemma guarded_product_block {m : Nat} (bits : Fin (2 * m) → Fin 2)
    (second : Bool) (output : Bits m)
    (coordinates : ∀ current, bits (position second current) = tupleCoordinates m output current)
    (current : Fin m) (bit : Fin 2) :
    (∏ previous : Fin (2 * m), recordFactor m bits (position second current) previous bit) =
      if bit = 0 then 1 else FourierScalar.before true output current := by
  have same :
      (∏ previous : Fin m,
        recordFactor m bits (position second current) (position second previous) bit) =
      if bit = 0 then 1 else FourierScalar.before true output current := by
    simp_rw [factor_same bits second output coordinates]
    by_cases zero : bit = 0
    · simp [zero]
    · simp only [if_neg zero, FourierScalar.before]
  have other :
      (∏ previous : Fin m,
        recordFactor m bits (position second current) (position (!second) previous) bit) = 1 := by
    apply Finset.prod_eq_one
    intro previous _
    exact factor_other bits second previous current bit
  rw [split_blocks]
  cases second with
  | false =>
      change (∏ previous : Fin m,
        recordFactor m bits (position false current) (position true previous) bit) = 1 at other
      rw [same, other, mul_one]
  | true =>
      change (∏ previous : Fin m,
        recordFactor m bits (position true current) (position false previous) bit) = 1 at other
      rw [other, same, one_mul]

/-- The physical output tuple is built from this actual measured path. -/
def blockOutput (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (second : Bool) : Bits m :=
  (binaryEquiv m).symm (BinaryBasis.bigEndianEquiv m (fun current =>
    ReadoutRows.outcomeBit width m (path (position second current)).2.1))

lemma blockOutput_coordinate (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (second : Bool) (current : Fin m) :
    tupleCoordinates m (blockOutput width m path second) current =
      ReadoutRows.outcomeBit width m (path (position second current)).2.1 := by
  simp only [blockOutput, tupleCoordinates, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Actual guarded Store feedback is exactly the within-block physical Fourier phase. -/
lemma feedback_block_on_path (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m (2 * m) id path original final)
    (second : Bool) (current : Fin m) (bit : Fin 2) :
    FeedbackRows.feedbackPhase width m (position second current)
        (path (position second current)).1 bit (Recovery.Layout.order m) =
      if bit = 0 then 1 else
        FourierScalar.before true (blockOutput width m path second) current := by
  rw [feedback_order_on_path width m path original final valid]
  apply guarded_product_block
  intro previous
  exact (blockOutput_coordinate width m path second previous).symm

/-- The actual per-block H/feedback coefficient has the exact negative Fourier row. -/
lemma actual_block_row (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m (2 * m) id path original final)
    (second : Bool) (input : Bits m) :
    (∏ current : Fin m,
      Gate.HOp (ReadoutRows.outcomeBit width m (path (position second current)).2.1)
          (tupleCoordinates m input current) *
        FeedbackRows.feedbackPhase width m (position second current)
          (path (position second current)).1 (tupleCoordinates m input current)
          (Recovery.Layout.order m)) =
      Partner.fourierRows true m (blockOutput width m path second) input := by
  rw [← FourierScalar.row_eq_fourier]
  unfold FourierScalar.row
  apply Finset.prod_congr rfl
  intro current _
  rw [blockOutput_coordinate, feedback_block_on_path width m path original final valid]

end

end ActualFeedback
end PointCoordinates.StageWord.PathWord.PathDensity
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
