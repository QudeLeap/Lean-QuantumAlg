/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Bounds

/-!
# Complete sequential depth of native four-branch execution

The bound charges initialization, the unmatched conditional source slot,
relative phase, and all preparation and unpreparation gates.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
noncomputable section

private theorem phaseDepth_bound (m n : Nat) : phaseDepth m n ≤ 40 * m + 20 := by
  cases n with
  | zero =>
      cases m with
      | zero => decide
      | succ k =>
          have bound := KnownZero.conjunction_bound k 1 (by decide)
          simp only [phaseDepth]
          omega
  | succ n =>
      have bound := KnownZero.conjunction_bound m (n + 1) (Nat.zero_lt_succ n)
      simp only [phaseDepth]
      omega

/-- The complete executed word has linear native depth in width times the longer phase length. -/
theorem totalComplexWord_depth_le {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    (complexWord U phases realAngle imaginaryAngle
      realConstant imaginaryConstant).evaluatedEventDepth (fun _ => 1) ≤
        (40 * m + 21) * (phases.length + 1) + 20 := by
  rw [totalComplexWord_depth, totalFourUnmatched_depth]
  have phaseBound := phaseDepth_bound m n
  have slots : (phaseDepth m n + 1) *
      (phases.length + 1) ≤ (40 * m + 21) * (phases.length + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_add, Nat.mul_one] at slots
  split_ifs <;> omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
