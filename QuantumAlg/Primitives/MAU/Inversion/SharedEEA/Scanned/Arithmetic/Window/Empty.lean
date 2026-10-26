/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Program

/-!
# Empty original arithmetic windows are exact complete-frame identities

The original native zero-width word emits no instruction, including in
signed mode with arbitrary Sign. Thus the scanned positive-window guard
may reject zero length without changing the source operation. This fact
does not justify rejecting any positive length or changing finite metadata.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticEmptyWindow

noncomputable section

open ArithmeticWindowProgram ArithmeticWindowRegisters

/-- All four actual original native zero-width arithmetic words are empty. -/
lemma focusGates_zero (operation : Operation) : focusGates 0 operation = [] := by
  cases operation <;> rfl

/-- The original actual empty word preserves its arbitrary overflow output and whole label. -/
lemma focusStep_zero {length : Nat} (empty : length = 0) (operation : Operation)
    (state : Addition.TTK.OverflowRegisters length) : focusStep operation state = state := by
  subst length
  have actual := focusGates_step 0 operation state
  rw [focusGates_zero] at actual
  exact actual.symm

/-- Empty remainder windows preserve every original work, metadata, flag and control field. -/
lemma remainderStep_empty {width : Nat} (window : Window width) (empty : window.length = 0)
    (operation : Operation) (state : Registers width) :
    ArithmeticWindowProgram.step window operation state = state := by
  apply (grouping window).injective
  rw [step_grouping, focusStep_zero empty]

/-- Coefficient orientation preserves the same complete original frame on empty windows. -/
lemma coefficientStep_empty {width : Nat} (window : Window width) (empty : window.length = 0)
    (operation : Operation) (state : Registers width) :
    CoefficientWindowProgram.step window operation state = state := by
  apply (CoefficientWindowOrientation.grouping window).injective
  rw [CoefficientWindowProgram.step_grouping, focusStep_zero empty]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticEmptyWindow
