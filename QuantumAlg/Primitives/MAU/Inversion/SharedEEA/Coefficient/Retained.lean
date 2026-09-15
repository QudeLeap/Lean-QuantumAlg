/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Phase.Action

/-!
# Complete original Work1 preservation through native coefficient arithmetic

The phase-three TTK operations read the reversed physical coefficient
window in Work1 and update Work2. Combining the exact source window with
its whole complementary prefix and suffix restores the complete original
Work1, including the unconsumed quotient and division remainder
[LYL+26, sec_EEA/sub_regshare.tex:288-296;
LYL+26, sec_EEA/sub_opt.tex:61-70]. No borrowed value is replaced by zero.

The final lemma identifies the actual guarded post-shift with its real
one-position rotation and finite increment on internally prepared phase
three. The gate program and its event trace remain the existing ones.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientRetained

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowProgram

private theorem arithmetic_firstWord {width : Nat} (selected : Window width)
    (operation : Operation) (state : Registers width) :
    (CoefficientWindowProgram.step selected operation state).firstWord = state.firstWord := by
  let output := CoefficientWindowProgram.step selected operation state
  have outside := congrArg (fun value : Complement selected => value.1)
    (CoefficientWindowLaws.step_complement selected operation state)
  change ((wordEquiv selected output.firstWord).1, (wordEquiv selected output.firstWord).2.2) =
    ((wordEquiv selected state.firstWord).1, (wordEquiv selected state.firstWord).2.2) at outside
  have reversed := congrArg (fun word : BitVec selected.length => word.reverse)
    (CoefficientWindowLaws.step_sourceWord selected operation state)
  change (output.firstWord.extractLsb' selected.below selected.length).reverse.reverse =
    (state.firstWord.extractLsb' selected.below selected.length).reverse.reverse at reversed
  rw [BitVec.reverse_reverse_eq, BitVec.reverse_reverse_eq] at reversed
  have source := (wordEquiv_window selected output.firstWord).trans
    (reversed.trans (wordEquiv_window selected state.firstWord).symm)
  apply (wordEquiv selected).injective
  exact Prod.ext
    (congrArg (fun pair : BitVec selected.above × BitVec selected.below => pair.1) outside)
    (Prod.ext source
      (congrArg (fun pair : BitVec selected.above × BitVec selected.below => pair.2) outside))

/-- Both real coefficient arithmetic instructions retain the complete original Work1. -/
theorem source_firstWord {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    (ArithmeticBlocks.coefficientSource state).firstWord = state.firstWord := by
  let selected := CoefficientWindowOrientation.coefficientWindow width
    (state.coefficientLength.toNat + 1) fits
  let current := ArithmeticInstruction.sourceStep .coefficientSubtract state
  have fields := CoefficientBlockLaws.subtraction_fields state first second fits
  change (ArithmeticInstruction.sourceStep .coefficientAdd
    (ArithmeticSign.coefficientStep current)).firstWord = _
  rw [CoefficientBlockLaws.source_add selected (ArithmeticSign.coefficientStep current)
    fields.2.1 (CoefficientBlockLaws.addition_window state first second fits), arithmetic_firstWord]
  change current.firstWord = state.firstWord
  dsimp only [current]
  rw [CoefficientBlockLaws.source_subtract state first second fits]
  split
  · rfl
  · exact arithmetic_firstWord selected .subtractLow state

/-- The same complete source preservation belongs to the emitted native coefficient block. -/
theorem native_firstWord (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true)
    (second : state.flags.second = false) (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    (ArithmeticBlocks.coefficientStep width state).firstWord = state.firstWord := by
  rw [ArithmeticBlocks.coefficientStep_eq_source width state clean]
  exact source_firstWord state first second fits

/-- The actual phase-three post-shift rotates once and increments its finite counter. -/
theorem post_shift_ascending (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true)
    (second : state.flags.second = false)
    (within : state.shift.toNat + 1 < 2 ^ width.size) :
    GuardedShift.step true state =
      { state with secondWord := state.secondWord.rotateLeft 1, shift := state.shift + 1 } := by
  rw [GuardedShift.step_eq_source width true state clean, GuardedShift.sourceStep,
    first, if_pos rfl, second]
  exact GuardedShift.ascending_eq_low state within

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientRetained
