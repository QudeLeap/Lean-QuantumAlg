/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Phase

/-!
# Original binary labels of the control-work phase

The last control is a separate original bit, between the first k controls
and the untouched signal suffix. Its decoded value is retained exactly.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
noncomputable section

private theorem lastControl_decoded (k n : Nat) (phase : Fin 2)
    (controls : Fin (2 ^ k)) (last : Fin 2) (signal : Fin (2 ^ n)) :
    (QuantumSignature.qubitsIndexEquiv (1 + (k + (1 + n)))).symm
      (prodEquiv (phase, prodEquiv (controls, prodEquiv (last, signal))))
      (lastControl k n) = last := by
  have outer := BinaryBasis.bigEndianEquiv_prod_right
    (leftWidth := 1) (rightWidth := k + (1 + n)) phase
    (prodEquiv (controls, prodEquiv (last, signal))) (Fin.natAdd k (0 : Fin (1 + n)))
  have middle := BinaryBasis.bigEndianEquiv_prod_right
    (leftWidth := k) (rightWidth := 1 + n) controls (prodEquiv (last, signal))
    (0 : Fin (1 + n))
  have inner := BinaryBasis.bigEndianEquiv_prod_left
    (leftWidth := 1) (rightWidth := n) last signal (0 : Fin 1)
  have single : (BinaryBasis.bigEndianEquiv 1).symm last 0 = last := by
    fin_cases last <;> rfl
  exact outer.trans (middle.trans (inner.trans single))

/-- Decoding observes precisely the first controls and the final original control. -/
theorem controlWork_phaseWeight_decoded (k n : Nat) (angle : ℝ) (phase : Fin 2)
    (controls : Fin (2 ^ k)) (last : Fin 2) (signal : Fin (2 ^ n)) :
    phaseWeight k n angle
      ((QuantumSignature.qubitsIndexEquiv (1 + (k + (1 + n)))).symm
        (prodEquiv (phase, prodEquiv (controls, prodEquiv (last, signal))))) =
      Gate.Rotation.Multiplex.weight
        (if controls = 0 ∧ last = 0 then -2 * angle else 2 * angle) phase := by
  unfold phaseWeight bits
  rw [controlLabel_decoded, lastControl_decoded, phase_decoded]

/-- Zero of the combined original control label means both original segments are zero. -/
theorem controlWork_zero_control_label (k : Nat) (controls : Fin (2 ^ k)) (last : Fin 2) :
    prodEquiv (m := k) (n := 1) (controls, last) = 0 ↔ controls = 0 ∧ last = 0 := by
  simp only [Fin.ext_iff]
  change last.val + 2 * controls.val = 0 ↔ controls.val = 0 ∧ last.val = 0
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
