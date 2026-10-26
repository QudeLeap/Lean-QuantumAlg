/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Nearest
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Probability
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Recovery

/-!
# Nearest recovery on strict full-range Fourier windows

Both raw frequencies may be any physical labels in their strict phase windows.
Nearest rescaling and modular wrap return the exact unit and negated hidden
frequency.  The original checked inverse and candidate reconstruction then
recover the secret with a true reconstruction flag.
-/

namespace QuantumAlg.EllipticCurve.FullRange

open FiniteCyclicDLP FiniteCyclicDLP.Canonical.Probability
open FiniteCyclicDLP.Canonical.Probability.RecoveryBridge
open ClassicalAlgorithms.Modular
open ClassicalRoutines.FiniteCyclicDLP

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Strict phase windows give the exact normalized residues consumed by the
checked inverse and candidate reconstruction, with the original right sign. -/
lemma nearest_normalize_eq_selected (problem : KnownOrderProblem G)
    (input : SecretInput problem) (unit : (ZMod problem.order)ˣ)
    (spec : ModulusSpec (orderWidth problem)) (sameOrder : spec.modulus = problem.order)
    (left right : Fin (2 ^ orderWidth problem))
    (leftWindow : qpePhaseDistance (orderWidth problem)
      (((unit : ZMod problem.order).val : ℝ) / problem.order) left <
        1 / (2 * problem.order))
    (rightWindow : qpePhaseDistance (orderWidth problem)
      (((-input.secret * (unit : ZMod problem.order)).val : ℝ) / problem.order) right <
        1 / (2 * problem.order)) :
    RawRecovery.Nearest.normalize spec left.val right.val =
      RawRecovery.normalize spec (selectedRawInput problem input unit) := by
  let : NeZero problem.order := ⟨problem.order_ne_zero⟩
  have widthPositive := modulusSpec_width_pos spec
  have leftValue := nearest_mod_eq_of_phase_window (orderWidth problem) problem.order
    (unit : ZMod problem.order).val widthPositive problem.order_pos
    (ZMod.val_lt _) left leftWindow
  have rightValue := nearest_mod_eq_of_phase_window (orderWidth problem) problem.order
    (-input.secret * (unit : ZMod problem.order)).val widthPositive problem.order_pos
    (ZMod.val_lt _) right rightWindow
  have leftEq : (RawRecovery.Nearest.normalize spec left.val right.val).left =
      (RawRecovery.normalize spec (selectedRawInput problem input unit)).left := by
    apply Fin.ext
    rw [RecoveryBridge.normalize_selectedRawInput_left_val problem input unit spec sameOrder]
    change NearestResidue.quotient (left.val * spec.modulus) (2 ^ orderWidth problem) %
      spec.modulus = _
    simpa only [sameOrder] using leftValue
  have rightEq : (RawRecovery.Nearest.normalize spec left.val right.val).right =
      (RawRecovery.normalize spec (selectedRawInput problem input unit)).right := by
    apply Fin.ext
    rw [RecoveryBridge.normalize_selectedRawInput_right_val problem input unit spec sameOrder]
    change NearestResidue.quotient (right.val * spec.modulus) (2 ^ orderWidth problem) %
      spec.modulus = _
    simpa only [sameOrder] using rightValue
  cases normalized : RawRecovery.normalize spec (selectedRawInput problem input unit)
  simp only [normalized] at leftEq rightEq
  cases nearest : RawRecovery.Nearest.normalize spec left.val right.val
  simp only [nearest] at leftEq rightEq
  cases leftEq
  cases rightEq
  rfl

/-- Any physical labels in the two strict windows recover the secret and pass
the reconstruction flag, including labels in the wrap-around parts of a window. -/
lemma nearest_outputOf_recovers (problem : KnownOrderProblem G)
    (input : SecretInput problem) (unit : (ZMod problem.order)ˣ)
    (spec : ModulusSpec (orderWidth problem)) (sameOrder : spec.modulus = problem.order)
    (left right : Fin (2 ^ orderWidth problem))
    (leftWindow : qpePhaseDistance (orderWidth problem)
      (((unit : ZMod problem.order).val : ℝ) / problem.order) left <
        1 / (2 * problem.order))
    (rightWindow : qpePhaseDistance (orderWidth problem)
      (((-input.secret * (unit : ZMod problem.order)).val : ℝ) / problem.order) right <
        1 / (2 * problem.order)) :
    ∃ output : ClassicalRoutines.FiniteCyclicDLP.Output spec,
      RawRecovery.Nearest.outputOf spec left.val right.val = some output ∧
      output.candidate.val = input.secret.val ∧ output.verified = true := by
  obtain ⟨output, recovered, candidate, verified⟩ :=
    RecoveryBridge.outputOf_selectedRawInput_recovers problem input unit spec sameOrder
  refine ⟨output, ?_, candidate, verified⟩
  unfold RawRecovery.Nearest.outputOf
  rw [nearest_normalize_eq_selected problem input unit spec sameOrder left right
    leftWindow rightWindow]
  exact recovered

/-- For prime subgroup order, every observable nonzero-character strict window
feeds nearest recovery with a unit and returns the correct verified candidate. -/
lemma recoverableWindow_nearest_output_recovers (problem : KnownOrderProblem G)
    (prime : problem.order.Prime) (input : SecretInput problem)
    (spec : ModulusSpec (orderWidth problem)) (sameOrder : spec.modulus = problem.order)
    (raw : Branch (orderWidth problem))
    (accepted : recoverableWindow (orderWidth problem) input.secret raw) :
    ∃ output : ClassicalRoutines.FiniteCyclicDLP.Output spec,
      RawRecovery.Nearest.outputOf spec raw.1.val raw.2.val = some output ∧
      output.candidate.val = input.secret.val ∧ output.verified = true := by
  let : Fact problem.order.Prime := ⟨prime⟩
  obtain ⟨frequency, nonzero, leftWindow, rightWindow⟩ := accepted
  exact nearest_outputOf_recovers problem input (Units.mk0 frequency nonzero) spec sameOrder
    raw.1 raw.2 leftWindow rightWindow

end

end QuantumAlg.EllipticCurve.FullRange
