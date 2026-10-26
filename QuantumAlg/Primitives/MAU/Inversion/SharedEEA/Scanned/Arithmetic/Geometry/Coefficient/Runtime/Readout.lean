/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Coefficient.Runtime

/-! # Full finite readouts and control commutation of the paid coefficient geometry -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit ArithmeticGuard NumberTheory.SharedEEA

/-- Runtime selection retains every original source position, including the selecting Phase2. -/
lemma runtimeCoefficientStep_source (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (runtimeCoefficientStep width positive state).1 = state.1 := by
  unfold runtimeCoefficientStep
  split <;> exact coefficientStep_source width positive _ state

/-- The whole original prefix and both physical metadata padding positions survive selection. -/
lemma runtimeCoefficientStep_prefix (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (runtimeCoefficientStep width positive state).2.2.1 = state.2.2.1 := by
  unfold runtimeCoefficientStep
  split <;> exact coefficientStep_prefix width positive _ state

/-- Both real source phases prepare precisely the complete mathematical finite length word. -/
lemma runtimeCoefficientStep_targetWord (width : Nat) (positive : 1 ≤ width) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : targetValue width state = 0#(fullWidth width)) :
    targetValue width (runtimeCoefficientStep width positive state) =
      ScanGeometry.coefficientWord state.1.flags.second state.1.coefficientLength
        state.1.divisorLength state.1.shift := by
  cases phase : state.1.flags.second with
  | false =>
      simpa only [runtimeCoefficientStep, phase, Bool.false_eq_true, if_false] using
        coefficientStep_targetWord width positive false state clean zero
  | true =>
      simpa only [runtimeCoefficientStep, phase, if_true] using
        coefficientStep_targetWord width positive true state clean zero

/-- Every finite metadata key is checked against its exact natural positive physical boundary. -/
lemma runtimeCoefficientStep_target_positive_iff (width : Nat) (positive : 1 ≤ width)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : targetValue width state = 0#(fullWidth width)) :
    (0 < (targetValue width (runtimeCoefficientStep width positive state)).toNat ∧
      (targetValue width (runtimeCoefficientStep width positive state)).toNat ≤ width + 3) ↔
      if state.1.flags.second then
        state.1.divisorLength.toNat + state.1.shift.toNat < width + 3
      else state.1.coefficientLength.toNat + 1 ≤ width + 3 := by
  rw [runtimeCoefficientStep_targetWord width positive state clean zero]
  exact ScanGeometry.coefficientWord_positive_iff _ _ _ _

private lemma coefficientStep_control_flip (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) :
    coefficientStep width positive deshift ((flag width 4).flip state) =
      (flag width 4).flip (coefficientStep width positive deshift state) := by
  apply data_eq_of_source_prefix_target width
  · change (coefficientStep width positive deshift ((flag width 4).flip state)).1 =
      { (coefficientStep width positive deshift state).1 with
        control := !(coefficientStep width positive deshift state).1.control }
    rw [coefficientStep_source, coefficientStep_source]
    rfl
  · change (coefficientStep width positive deshift ((flag width 4).flip state)).2.2.1 =
      (coefficientStep width positive deshift state).2.2.1
    rw [coefficientStep_prefix, coefficientStep_prefix]
    rfl
  · change targetValue width
      (coefficientStep width positive deshift ((flag width 4).flip state)) =
        targetValue width (coefficientStep width positive deshift state)
    rw [coefficientStep_targetValue, coefficientStep_targetValue]
    cases deshift <;> rfl

/-- Original Ctrl can change before the actual adjoint without changing the prepared geometry. -/
lemma runtimeCoefficientStep_control_flip (width : Nat) (positive : 1 ≤ width)
    (state : Data width) :
    runtimeCoefficientStep width positive ((flag width 4).flip state) =
      (flag width 4).flip (runtimeCoefficientStep width positive state) := by
  have samePhase : ((flag width 4).flip state).1.flags.second = state.1.flags.second := rfl
  unfold runtimeCoefficientStep
  rw [samePhase]
  split <;> exact coefficientStep_control_flip width positive _ state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
