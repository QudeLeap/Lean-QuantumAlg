/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Execution
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Bounds

/-!
# Complete sequential depth of native four-branch execution

The bound charges initialization, the unmatched conditional source slot,
relative phase, and all preparation and unpreparation gates.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

/-- The complete executed word has linear native depth in width times the longer phase length. -/
lemma complexWord_depth_le {m n : Nat}
    (positive : 0 < n) (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    (complexWord (m := m) (n := n) positive phases realAngle imaginaryAngle
      realConstant imaginaryConstant).evaluatedEventDepth (fun _ => 1) ≤
        (20 * m + 13) * (phases.length + 1) + 20 := by
  rw [complexWord_depth, fourUnmatched_depth]
  have conjunction := KnownZero.conjunction_bound m n positive
  have slots : (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 11) *
      (phases.length + 1) ≤ (20 * m + 13) * (phases.length + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_add, Nat.mul_one] at slots
  split_ifs <;> omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
