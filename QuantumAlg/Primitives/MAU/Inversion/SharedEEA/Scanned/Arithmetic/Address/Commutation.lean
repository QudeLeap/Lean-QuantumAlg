/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Coefficient.Runtime

/-!
# Complete physical address preparation commutes with retained-source arithmetic

The source transform may change both work words and Sign. It must retain
the complete original metadata and Phase2, and its lift keeps the entire
physical pool. The resulting equality concerns the complete state, so it
can justify actual address uncomputation after the real arithmetic body.
No source transform is constructed or executed by this lemma.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- A declared original-frame transform retains every physical pool position in its lift. -/
def liftSource (width : Nat) (transform : Registers width → Registers width)
    (state : Data width) : Data width := (transform state.1, state.2)

/-- The actual phase-controlled address has the full finite native modular equation. -/
lemma runtimeCoefficientStep_address (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (runtimeCoefficientStep width positive state).2.1 =
      if state.1.flags.second then (state.2.1 ^^^ coefficientConstant width) -
        sourceValue width positive .divisor state - sourceValue width positive .shift state
      else sourceValue width positive .coefficient state + state.2.1 := by
  unfold runtimeCoefficientStep
  split_ifs <;> exact coefficientStep_address width positive _ state

/-- Retaining full original metadata gives the same actual padded address-adder operand. -/
lemma sourceValue_liftSource (width : Nat) (positive : 1 ≤ width)
    (transform : Registers width → Registers width) (state : Data width)
    (field : ArithmeticGeometry.Field)
    (retained : ArithmeticGeometry.fieldValue field (liftSource width transform state) =
      ArithmeticGeometry.fieldValue field state) :
    sourceValue width positive field (liftSource width transform state) =
      sourceValue width positive field state := by
  unfold sourceValue
  rw [retained]
  rfl

/-- Complete native coefficient address action commutes with the full retained-source transform. -/
lemma runtimeCoefficientStep_liftSource (width : Nat) (positive : 1 ≤ width)
    (transform : Registers width → Registers width) (state : Data width)
    (retained : ∀ field, ArithmeticGeometry.fieldValue field (liftSource width transform state) =
      ArithmeticGeometry.fieldValue field state)
    (phase : (transform state.1).flags.second = state.1.flags.second) :
    runtimeCoefficientStep width positive (liftSource width transform state) =
      liftSource width transform (runtimeCoefficientStep width positive state) := by
  apply Prod.ext
  · change (runtimeCoefficientStep width positive (liftSource width transform state)).1 =
      transform (runtimeCoefficientStep width positive state).1
    rw [runtimeCoefficientStep_source, runtimeCoefficientStep_source]
    rfl
  · apply Prod.ext
    · change (runtimeCoefficientStep width positive (liftSource width transform state)).2.1 =
        (runtimeCoefficientStep width positive state).2.1
      rw [runtimeCoefficientStep_address, runtimeCoefficientStep_address]
      rw [sourceValue_liftSource width positive transform state .divisor (retained .divisor),
        sourceValue_liftSource width positive transform state .shift (retained .shift),
        sourceValue_liftSource width positive transform state .coefficient
          (retained .coefficient)]
      simp only [liftSource, phase]
    · change (runtimeCoefficientStep width positive (liftSource width transform state)).2.2 =
        (runtimeCoefficientStep width positive state).2.2
      rw [runtimeCoefficientStep_workspace, runtimeCoefficientStep_workspace]
      rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
