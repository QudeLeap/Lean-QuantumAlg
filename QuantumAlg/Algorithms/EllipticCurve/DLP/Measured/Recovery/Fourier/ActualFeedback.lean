/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Literal feedback scalars on each legal complete Store path

The theorem uses the actual point-retained Store and actual readout writes in
traceValid. It does not replace measured paths by exponent labels or add their Kraus
matrices coherently. The within-block feeds guard is retained verbatim.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.PathDensity
namespace ActualFeedback

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.QuantumFourierTransform
open Recovery.Stage.PointCoordinates
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

/-- A single actual guarded feedback scalar expressed by its earlier measured bit. -/
def recordFactor (m : Nat) (bits : Fin (2 * m) → Fin 2)
    (current previous : Fin (2 * m)) (bit : Fin 2) : ℂ :=
  if Recovery.Layout.feeds m previous current then
    if bits previous = 1 then
      if bit = 0 then 1 else
        Semiclassical.Partner.rotation true (current.val - previous.val - 1)
    else 1
  else 1

lemma feedbackOne_on_path (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Interface width m))
    (valid : traceValid width m (2 * m) id path original final)
    (previous current : Fin (2 * m)) (bit : Fin 2) :
    FeedbackRows.feedbackOnePhase width m previous current (path current).1 bit =
      recordFactor m (fun index => ReadoutRows.outcomeBit width m (path index).2.1)
        current previous bit := by
  by_cases enabled : Recovery.Layout.feeds m previous current
  · simp only [FeedbackRows.feedbackOnePhase, recordFactor, if_pos enabled]
    rw [FeedbackReads.full_trace_feedback_read width m path original final valid
      previous current enabled]
    change (if (ReadoutRows.outcomeBit width m (path previous).2.1).val = 1 then
      FeedbackRows.nativePhase (-Source.phaseAngle (current.val - previous.val - 1)) bit
      else 1) =
        if ReadoutRows.outcomeBit width m (path previous).2.1 = 1 then
          if bit = 0 then 1 else
            Semiclassical.Partner.rotation true (current.val - previous.val - 1)
        else 1
    by_cases selected : ReadoutRows.outcomeBit width m (path previous).2.1 = 1
    · rw [selected]
      change FeedbackRows.nativePhase (-Source.phaseAngle (current.val - previous.val - 1)) bit =
        if bit = 0 then 1 else
          Semiclassical.Partner.rotation true (current.val - previous.val - 1)
      simp [FeedbackRows.nativePhase, Semiclassical.Partner.rotation]
    · have notSelected : (ReadoutRows.outcomeBit width m (path previous).2.1).val ≠ 1 := by
        intro same
        exact selected (Fin.ext same)
      rw [if_neg notSelected, if_neg selected]
  · simp only [FeedbackRows.feedbackOnePhase, recordFactor, if_neg enabled]

/-- Literal list order is changed only inside the commutative scalar product. -/
lemma feedback_list_on_path (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Interface width m))
    (valid : traceValid width m (2 * m) id path original final)
    (current : Fin (2 * m)) (bit : Fin 2) (indices : List (Fin (2 * m))) :
    FeedbackRows.feedbackPhase width m current (path current).1 bit indices =
      (indices.map (fun previous =>
        recordFactor m (fun index => ReadoutRows.outcomeBit width m (path index).2.1)
          current previous bit)).prod := by
  induction indices with
  | nil => rfl
  | cons previous tail ih =>
      exact (congrArg₂ (fun first second : ℂ => first * second) ih
        (feedbackOne_on_path width m path original final valid previous current bit)).trans
          (mul_comm _ _)

/-- Every actual stage's feedback is the product over its real earlier measured cells. -/
lemma feedback_order_on_path (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Interface width m))
    (valid : traceValid width m (2 * m) id path original final)
    (current : Fin (2 * m)) (bit : Fin 2) :
    FeedbackRows.feedbackPhase width m current (path current).1 bit (Recovery.Layout.order m) =
      ∏ previous : Fin (2 * m),
        recordFactor m (fun index => ReadoutRows.outcomeBit width m (path index).2.1)
          current previous bit := by
  rw [feedback_list_on_path width m path original final valid current bit]
  exact (Fin.prod_univ_def _).symm

end

end ActualFeedback
end PointCoordinates.StageWord.PathWord.PathDensity
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
