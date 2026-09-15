/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Bound

/-!
# Pure recovery from the actual selected exponent bits

The measured bit mask is placed in the original raw recovery shape in its
unchanged big-endian order. Membership in the original selected event implies
that the existing decoder, rescaling, checked inverse and reconstruction check
return the advertised secret. The secret is only a mathematical witness.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open FiniteCyclicDLP Canonical.Probability
open ClassicalAlgorithms.Modular
open ScalarMultiplication.MeasuredPlacement.Allocation

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Reinterpret the actual ordered mask in the original raw shape, without changing a bit. -/
def rawExponentInput (problem : KnownOrderProblem E.GroupPoint)
    (bits : Fin (2 * orderWidth problem) → Bool) :
    CShape.Value (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.InputShape
      (orderWidth problem)) :=
  .bits (fun index => bits (Fin.cast (by omega) index))

/-- The original packed pair and the actual mask agree at every physical bit. -/
theorem rawExponentInput_pair (problem : KnownOrderProblem E.GroupPoint)
    (frequency : Fin (2 ^ orderWidth problem) × Fin (2 ^ orderWidth problem)) :
    rawExponentInput problem
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) frequency) =
      .bits (Canonical.BornBridge.measurementOutcome problem (prodEquiv frequency)) := by
  apply congrArg CShape.Value.bits
  funext index
  change ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem) frequency
    (Fin.cast (by omega) index) =
      (prodEquiv frequency).val.testBit
        (orderWidth problem + orderWidth problem - 1 - index.val)
  rw [← pairedBranch_bit]
  apply congrArg (prodEquiv frequency).val.testBit
  rw [Fin.val_rev, Fin.val_cast]
  omega

/-- A selected unit gives precisely the original selected raw recovery input. -/
theorem rawExponentInput_selected (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) (unit : (ZMod problem.order)ˣ) :
    rawExponentInput problem
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
        (selectedExponentFrequency problem input unit)) =
      RecoveryBridge.selectedRawInput problem input unit := by
  exact rawExponentInput_pair problem _

/-- Existing pure recovery computes the advertised secret on every original selected unit. -/
theorem outputOf_selectedExponentFrequency_recovers
    (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem)
    (unit : (ZMod problem.order)ˣ) (spec : ModulusSpec (orderWidth problem))
    (sameOrder : spec.modulus = problem.order) :
    ∃ output : ClassicalRoutines.FiniteCyclicDLP.Output spec,
      ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputOf spec
        (rawExponentInput problem
          (ExceptionalOffsetAveraging.pairedBigEndianSelected (orderWidth problem)
            (selectedExponentFrequency problem input unit))) = some output ∧
      output.candidate.val = input.secret.val ∧ output.verified = true := by
  rw [rawExponentInput_selected]
  exact RecoveryBridge.outputOf_selectedRawInput_recovers problem input unit spec sameOrder

/-- Membership of the actual measured mask suffices for candidate recovery and verification. -/
theorem outputOf_selectedExponentEvent_recovers
    (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem)
    (bits : Fin (2 * orderWidth problem) → Bool)
    (selected : selectedExponentEvent problem input bits = true)
    (spec : ModulusSpec (orderWidth problem)) (sameOrder : spec.modulus = problem.order) :
    ∃ output : ClassicalRoutines.FiniteCyclicDLP.Output spec,
      ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputOf spec
        (rawExponentInput problem bits) = some output ∧
      output.candidate.val = input.secret.val ∧ output.verified = true := by
  classical
  obtain ⟨unit, rfl⟩ := of_decide_eq_true selected
  exact outputOf_selectedExponentFrequency_recovers problem input unit spec sameOrder

/-- The original three-cell recovery model encodes success, the secret and reconstruction. -/
theorem outputCells_selectedExponentEvent
    (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem)
    (bits : Fin (2 * orderWidth problem) → Bool)
    (selected : selectedExponentEvent problem input bits = true)
    (spec : ModulusSpec (orderWidth problem)) (sameOrder : spec.modulus = problem.order) :
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells spec
      (rawExponentInput problem bits) =
      .product (.bit true)
        (.product (CShape.wordOfNat (orderWidth problem) input.secret.val) (.bit true)) := by
  obtain ⟨output, success, candidate, verified⟩ :=
    outputOf_selectedExponentEvent_recovers problem input bits selected spec sameOrder
  rw [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells_of_outputOf_some
    spec _ output success, candidate, verified]

/-- A nontrivial order yields the local fixed-width modulus required by the raw model. -/
def recoveryModulusSpec (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) : ModulusSpec (orderWidth problem) where
  modulus := problem.order
  two_le := nontrivial
  le_capacity := order_le_fourierModulus problem

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
