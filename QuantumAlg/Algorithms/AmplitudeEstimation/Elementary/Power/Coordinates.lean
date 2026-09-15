/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Layout
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Util.FinPow

/-!
# The original binary exponent inside the complete physical phase prefix

The selected exceptional work position is a suffix of the original phase
register. Taking its actual tensor factor apart shows that every power stage
still reads the same original bit. The work value contributes no exponent.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

/-- The original phase value of the explicitly split physical phase/work prefix. -/
def originalPhase (t n : Nat) (phase : Fin (2 ^ phaseWidth t n)) : Fin (2 ^ t) :=
  ((prodEquiv (m := t) (n := helperWidth t n)).symm phase).1

/-- The value of the explicitly present work factor, including its unique value at width zero. -/
def workPhase (t n : Nat) (phase : Fin (2 ^ phaseWidth t n)) : Fin (2 ^ helperWidth t n) :=
  ((prodEquiv (m := t) (n := helperWidth t n)).symm phase).2

theorem originalPhase_prod (t n : Nat) (phase : Fin (2 ^ t))
    (work : Fin (2 ^ helperWidth t n)) :
    originalPhase t n (prodEquiv (phase, work)) = phase := by
  simp only [originalPhase, Equiv.symm_apply_apply]

theorem workPhase_prod (t n : Nat) (phase : Fin (2 ^ t))
    (work : Fin (2 ^ helperWidth t n)) : workPhase t n (prodEquiv (phase, work)) = work := by
  simp only [workPhase, Equiv.symm_apply_apply]

/-- The extended physical stage reads the original bit and ignores the arbitrary work value. -/
theorem extendedStage_testBit {t : Nat} (n : Nat) (stage : Fin t)
    (phase : Fin (2 ^ phaseWidth t n)) :
    phase.val.testBit (extendedStage n stage).val =
      (originalPhase t n phase).val.testBit stage.val := by
  obtain ⟨⟨original, work⟩, rfl⟩ :=
    (prodEquiv (m := t) (n := helperWidth t n)).surjective phase
  rw [originalPhase_prod]
  change (prodEquiv (original, work)).val.testBit (stage.val + helperWidth t n) = _
  rw [Nat.add_comm stage.val (helperWidth t n)]
  exact prodEquiv_testBit_left original work stage

/-- The literal original power multiplicity is unchanged by physical placement. -/
theorem extendedStage_exponent {t : Nat} (n : Nat) (stage : Fin t)
    (phase : Fin (2 ^ phaseWidth t n)) :
    2 ^ stage.val * (phase.val.testBit (extendedStage n stage).val).toNat =
      qpeStageExponent stage (originalPhase t n phase) := by
  rw [extendedStage_testBit]
  rfl

/-- Every source and selected work value appears in the explicit full-register reassociation. -/
theorem originalAndWorkEquiv_pair (t n : Nat) (phase : Fin (2 ^ phaseWidth t n))
    (source : Fin (2 ^ n)) :
    originalAndWorkEquiv t n (prodEquiv (phase, source)) =
      (prodEquiv (originalPhase t n phase, source), workPhase t n phase) := by
  obtain ⟨⟨original, work⟩, rfl⟩ :=
    (prodEquiv (m := t) (n := helperWidth t n)).surjective phase
  rw [originalPhase_prod, workPhase_prod, originalAndWorkEquiv_apply]

end

end QuantumAlg.AmplitudeEstimation.Elementary
