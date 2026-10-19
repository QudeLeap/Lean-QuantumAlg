/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Depth
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
import QuantumAlg.Util.Nat.ChooseTwo

/-!
# Closed polynomial coordinates for the existing ECDLP execution

These identities expose the same native resource allowances without changing
the selected execution, its memory roles or its original field arithmetic.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

private lemma pairs_identity (width : Nat) :
    2 * Nat.choose width 2 + width = width ^ 2 := by
  rw [ChooseTwo.twice_choose_two]
  cases width <;> simp
  ring

/-- The actual native CNOT allowance has the stated quadratic form. -/
lemma real_cnot_closed (t : Nat) :
    Scalar.roundCnot t = 2 * t ^ 2 + 4 * t + 6 * (t / 2) := by
  have pairs := pairs_identity t
  unfold Scalar.roundCnot
  nlinarith

/-- Both resets, native preparation and Fourier phases retain their original gate count. -/
lemma real_single_closed (f t : Nat) :
    Scalar.roundSingleQubit f t = 3 * t ^ 2 + 25 * t + 4 * f + 3 := by
  have pairs := pairs_identity t
  unfold Scalar.roundSingleQubit Scalar.qubits
  nlinarith

/-- Native checked recovery retains exactly the same classical operation allowance. -/
lemma real_classical_closed (f t : Nat) :
    Scalar.recoveryEvents f t = 248 * f * t + 686 * t + 119 := by
  unfold Scalar.recoveryEvents
  ring

/-- The retained and temporary words expand to the same classical memory ceiling. -/
lemma real_resident_closed (f t : Nat) :
    Scalar.residentBits f t =
      max (18 * t ^ 2 + 70 * t + 70) (18 * f ^ 2 + 72 * f + 69) +
        6 * f + 4 * t + 8 := by
  unfold Scalar.residentBits Scalar.scratchBits Scalar.coefficientBits
  congr 4 <;> ring

/-- The first complete round has this closed auxiliary unit-event bound. -/
lemma real_event_unit_depth_closed (f t : Nat) :
    quantumEventRoundDepthBound f t + 1 =
      (5 * t ^ 2 + 37 * t) / 2 + 8 * f + 3 * (t / 2) + 8 := by
  have pairs := pairs_identity t
  have numerator : 5 * t ^ 2 + 37 * t = 2 * (5 * Nat.choose t 2 + 21 * t) := by
    nlinarith
  rw [numerator, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  unfold quantumEventRoundDepthBound Scalar.qubits
  omega

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
