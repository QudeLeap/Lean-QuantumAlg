/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Blocks
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Laws
import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Scale

/-!
# Actual phase-two remainder subtraction, Sign complement, and add-back

The actual source window excludes the final shift bits of Work1 and Work2
[LYL+26, sec_EEA/sub_regshare.tex:263-278]. The complete native block
subtracts on the high window with Sign, complements Sign, and adds back
exactly on underflow [LYL+26, sec_EEA/sub_opt.tex:43-48]. Its resulting
upper word is `SignedDivision.corrected`, and Sign is the weak-comparison
digit subsequently exchanged into the quotient. Equality therefore writes
one without changing the original input domain.

The complete complementary tuple retains every low shift bit, even when
that suffix is nonzero. `DivisionScale` reassembles this actual upper-word
subtraction with that retained suffix; the upper word is not silently
identified with the complete remainder. Phase, zero Sign, physical fit,
and native Ctrl zero are local reachable-state invariants, to be supplied
by the actual phase trajectory rather than by an eventual caller.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.RemainderBlockLaws

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowProgram ArithmeticWindowLaws
open NumberTheory.SharedEEA

/-- The actual upper remainder region, leaving the full low shift suffix outside the arithmetic. -/
def window {width : Nat} (state : Registers width)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) : Window width :=
  remainderWindow width (state.coefficientLength.toNat + state.quotientLength.toNat + 1)
    state.shift.toNat fits

private lemma arithmetic_phase {width : Nat} (selected : Window width) (operation : Operation)
    (state : Registers width) :
    ((ArithmeticWindowProgram.step selected operation state).flags.first,
      (ArithmeticWindowProgram.step selected operation state).flags.second) =
      (state.flags.first, state.flags.second) :=
  congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1)
    (ArithmeticWindowPreservation.remainder_retained selected operation state)

private lemma marked_sign {width : Nat} (selected : Window width) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true) :
    (ArithmeticSign.remainderStep
      (ArithmeticWindowProgram.step selected .subtractSigned state)).flags.sign =
      !(ArithmeticWindowProgram.step selected .subtractSigned state).flags.sign := by
  have phase := arithmetic_phase selected .subtractSigned state
  have firstSame := congrArg (fun pair : Bool × Bool => pair.1) phase
  have secondSame := congrArg (fun pair : Bool × Bool => pair.2) phase
  change (ArithmeticWindowProgram.step selected .subtractSigned state).flags.first =
    state.flags.first at firstSame
  change (ArithmeticWindowProgram.step selected .subtractSigned state).flags.second =
    state.flags.second at secondSame
  change ((ArithmeticWindowProgram.step selected .subtractSigned state).flags.sign ^^
    (!(ArithmeticWindowProgram.step selected .subtractSigned state).flags.first &&
      (ArithmeticWindowProgram.step selected .subtractSigned state).flags.second)) = _
  rw [firstSame, secondSame, first, second]
  exact Bool.xor_true _

/-- Zero divisor rejects both actual remainder bodies while retaining the literal Sign gate. -/
lemma source_finished {width : Nat} (state : Registers width)
    (finished : state.divisorLength = 0) :
    ArithmeticBlocks.remainderSource state = ArithmeticSign.remainderStep state := by
  have subtract : ArithmeticInstruction.sourceStep .remainderSubtract state = state := by
    rw [ArithmeticInstruction.sourceStep,
      ArithmeticInstruction.sourceEnabled_terminal .remainderSubtract rfl state finished]
    rfl
  rw [ArithmeticBlocks.remainderSource, subtract, ArithmeticInstruction.sourceStep,
    ArithmeticInstruction.sourceEnabled_terminal .remainderAddback rfl
      (ArithmeticSign.remainderStep state) finished]
  rfl

private lemma source_subtract {width : Nat} (selected : Window width) (state : Registers width)
    (first : state.flags.first = false)
    (divisor : state.divisorLength ≠ 0)
    (physical : ArithmeticInstruction.sourceWindow .remainderSubtract state = some selected) :
    ArithmeticInstruction.sourceStep .remainderSubtract state =
      ArithmeticWindowProgram.step selected .subtractSigned state := by
  rw [ArithmeticInstruction.sourceStep,
    ArithmeticInstruction.sourceEnabled_active .remainderSubtract state divisor]
  change (if !state.flags.first then
    match ArithmeticInstruction.sourceWindow .remainderSubtract state with
    | some region => ArithmeticSelector.bodyStep region .subtractSigned false state
    | none => state
    else state) = _
  rw [first, physical]
  rfl

private lemma source_addback {width : Nat} (selected : Window width) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (divisor : state.divisorLength ≠ 0)
    (physical : ArithmeticInstruction.sourceWindow .remainderAddback state = some selected) :
    ArithmeticInstruction.sourceStep .remainderAddback state =
      if state.flags.sign then state else
        ArithmeticWindowProgram.step selected .addLow state := by
  have enabled :
      ArithmeticInstruction.sourceEnabled .remainderAddback state = !state.flags.sign := by
    rw [ArithmeticInstruction.sourceEnabled_active .remainderAddback state divisor]
    change (!state.flags.first && (!state.flags.second || !state.flags.sign)) = _
    rw [first, second]
    rfl
  rw [ArithmeticInstruction.sourceStep, enabled, physical]
  cases state.flags.sign <;> rfl

private lemma subtract_window {width : Nat} (state : Registers width)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 +
      state.shift.toNat ≤ width + 3) :
    ArithmeticInstruction.sourceWindow .remainderSubtract state =
      some (window state fits) := by
  change (if bound : state.coefficientLength.toNat + state.quotientLength.toNat + 1 +
      state.shift.toNat ≤ width + 3 then
    some (remainderWindow width
      (state.coefficientLength.toNat + state.quotientLength.toNat + 1) state.shift.toNat bound)
    else none) = _
  rw [dif_pos fits]
  rfl

private lemma marked_divisor {width : Nat} (state : Registers width)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 +
      state.shift.toNat ≤ width + 3) (divisor : state.divisorLength ≠ 0) :
    (ArithmeticSign.remainderStep
      (ArithmeticWindowProgram.step (window state fits) .subtractSigned state)).divisorLength ≠
        0 := by
  have retained := ArithmeticWindowPreservation.remainder_retained
    (window state fits) .subtractSigned state
  have same : (ArithmeticSign.remainderStep
      (ArithmeticWindowProgram.step (window state fits) .subtractSigned state)).divisorLength =
        state.divisorLength :=
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.1)
      retained
  exact fun zero => divisor (same.symm.trans zero)

private lemma marked_phase {width : Nat} (selected : Window width)
    (state : Registers width) :
    ((ArithmeticSign.remainderStep
      (ArithmeticWindowProgram.step selected .subtractSigned state)).flags.first,
      (ArithmeticSign.remainderStep
        (ArithmeticWindowProgram.step selected .subtractSigned state)).flags.second) =
      (state.flags.first, state.flags.second) :=
  arithmetic_phase selected .subtractSigned state

private lemma source_after_subtraction {width : Nat} (selected : Window width)
    (state : Registers width) (first : state.flags.first = false)
    (divisor : state.divisorLength ≠ 0)
    (physical : ArithmeticInstruction.sourceWindow .remainderSubtract state =
      some selected) :
    ArithmeticBlocks.remainderSource state =
      ArithmeticInstruction.sourceStep .remainderAddback
        (ArithmeticSign.remainderStep
          (ArithmeticWindowProgram.step selected .subtractSigned state)) :=
  congrArg (fun current => ArithmeticInstruction.sourceStep .remainderAddback
    (ArithmeticSign.remainderStep current))
    (source_subtract selected state first divisor physical)

private lemma addback_window {width : Nat} (state : Registers width)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 +
      state.shift.toNat ≤ width + 3) :
    let selected := window state fits
    let subtracted := ArithmeticWindowProgram.step selected .subtractSigned state
    ArithmeticInstruction.sourceWindow .remainderAddback
      (ArithmeticSign.remainderStep subtracted) = some selected := by
  intro selected subtracted
  have retained := ArithmeticWindowPreservation.remainder_retained selected .subtractSigned state
  have coefficientSame :=
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.1.1) retained
  have quotientSame :=
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.1.2) retained
  have shiftSame :=
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.2) retained
  change subtracted.coefficientLength = state.coefficientLength at coefficientSame
  change subtracted.quotientLength = state.quotientLength at quotientSame
  change subtracted.shift = state.shift at shiftSame
  change (if bound : subtracted.coefficientLength.toNat + subtracted.quotientLength.toNat + 1 +
      subtracted.shift.toNat ≤ width + 3 then
    some (remainderWindow width
      (subtracted.coefficientLength.toNat + subtracted.quotientLength.toNat + 1)
      subtracted.shift.toNat bound) else none) = _
  rw [coefficientSame, quotientSame, shiftSame, dif_pos fits]
  rfl

private lemma source_eq_preSign {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    let selected := window state fits
    let subtracted := ArithmeticWindowProgram.step selected .subtractSigned state
    let marked := ArithmeticSign.remainderStep subtracted
    ArithmeticBlocks.remainderSource state =
      if marked.flags.sign then marked else
        ArithmeticWindowProgram.step selected .addLow marked := by
  intro selected subtracted marked
  have subtractWindow : ArithmeticInstruction.sourceWindow .remainderSubtract state =
      some selected := subtract_window state fits
  have markedDivisor : marked.divisorLength ≠ 0 := marked_divisor state fits divisor
  have phase := marked_phase selected state
  have firstMarked : marked.flags.first = false :=
    (congrArg (fun pair : Bool × Bool => pair.1) phase).trans first
  have secondMarked : marked.flags.second = true :=
    (congrArg (fun pair : Bool × Bool => pair.2) phase).trans second
  have addbackWindow : ArithmeticInstruction.sourceWindow .remainderAddback marked =
      some selected := addback_window state fits
  calc
    ArithmeticBlocks.remainderSource state =
        ArithmeticInstruction.sourceStep .remainderAddback marked := by
      exact source_after_subtraction selected state first divisor subtractWindow
    _ = if marked.flags.sign then marked else
        ArithmeticWindowProgram.step selected .addLow marked :=
      source_addback selected marked firstMarked secondMarked markedDivisor addbackWindow

private lemma conditional_flip {α : Type} (flag other : Bool)
    (unchanged body : α) (complement : other = !flag) :
    (if other then unchanged else body) =
      (if flag then body else unchanged) := by
  rw [complement]
  cases flag <;> rfl

/-- The actual phase-two block adds back precisely on the original signed subtraction's borrow. -/
lemma source_eq {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    let selected := window state fits
    let subtracted := ArithmeticWindowProgram.step selected .subtractSigned state
    let marked := ArithmeticSign.remainderStep subtracted
    ArithmeticBlocks.remainderSource state =
      if subtracted.flags.sign then
        ArithmeticWindowProgram.step selected .addLow marked else marked := by
  intro selected subtracted marked
  calc
    ArithmeticBlocks.remainderSource state =
        if marked.flags.sign then marked else
          ArithmeticWindowProgram.step selected .addLow marked :=
      source_eq_preSign state first second divisor fits
    _ = if subtracted.flags.sign then
        ArithmeticWindowProgram.step selected .addLow marked else marked :=
      conditional_flip subtracted.flags.sign marked.flags.sign marked
        (ArithmeticWindowProgram.step selected .addLow marked)
        (marked_sign selected state first second)

/-- The actual upper remainder output is precisely conditional subtraction with unsigned borrow. -/
lemma source_target {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (zeroSign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    targetWord (window state fits) (ArithmeticBlocks.remainderSource state) =
      SignedDivision.corrected (targetWord (window state fits) state)
        (sourceWord (window state fits) state) := by
  let selected := window state fits
  let subtracted := ArithmeticWindowProgram.step selected .subtractSigned state
  rw [source_eq state first second divisor fits]
  rw [step_subtract_sign selected state zeroSign]
  dsimp only [SignedDivision.corrected]
  change targetWord selected
      (if decide ((targetWord selected state).toNat < (sourceWord selected state).toNat) then
        ArithmeticWindowProgram.step selected .addLow (ArithmeticSign.remainderStep subtracted)
      else ArithmeticSign.remainderStep subtracted) =
    (if (SignedDivision.difference (targetWord selected state) (sourceWord selected state)).msb then
      (SignedDivision.difference (targetWord selected state) (sourceWord selected state)).setWidth
        selected.length + sourceWord selected state
    else (SignedDivision.difference (targetWord selected state)
      (sourceWord selected state)).setWidth selected.length)
  rw [SignedDivision.difference_sign, SignedDivision.difference_low]
  by_cases borrowed : (targetWord selected state).toNat < (sourceWord selected state).toNat
  · rw [decide_eq_true borrowed]
    change targetWord selected
      (ArithmeticWindowProgram.step selected .addLow (ArithmeticSign.remainderStep subtracted)) =
      (targetWord selected state - sourceWord selected state) + sourceWord selected state
    rw [step_low_add]
    change targetWord selected subtracted + sourceWord selected subtracted = _
    rw [step_subtract_low selected state zeroSign, step_sourceWord]
  · rw [decide_eq_false borrowed]
    change targetWord selected subtracted = targetWord selected state - sourceWord selected state
    exact step_subtract_low selected state zeroSign

/-- The real Sign before quotient exchange is the weak full-window comparison digit. -/
lemma source_sign {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (zeroSign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    (ArithmeticBlocks.remainderSource state).flags.sign =
      decide ((sourceWord (window state fits) state).toNat ≤
        (targetWord (window state fits) state).toNat) := by
  let selected := window state fits
  let subtracted := ArithmeticWindowProgram.step selected .subtractSigned state
  let marked := ArithmeticSign.remainderStep subtracted
  have resultSign : (ArithmeticBlocks.remainderSource state).flags.sign = marked.flags.sign := by
    rw [source_eq state first second divisor fits]
    split
    · exact ArithmeticWindowPreservation.remainder_sign selected .addLow marked rfl
    · rfl
  rw [resultSign, marked_sign selected state first second,
    step_subtract_sign selected state zeroSign]
  change (!decide ((targetWord selected state).toNat < (sourceWord selected state).toNat)) =
    decide ((sourceWord selected state).toNat ≤ (targetWord selected state).toNat)
  by_cases ordered : (sourceWord selected state).toNat ≤ (targetWord selected state).toNat
  · have notBorrowed : ¬(targetWord selected state).toNat < (sourceWord selected state).toNat :=
      Nat.not_lt.mpr ordered
    simp only [decide_eq_false notBorrowed, Bool.not_false, decide_eq_true ordered]
  · have borrowed : (targetWord selected state).toNat < (sourceWord selected state).toNat :=
      Nat.lt_of_not_ge ordered
    simp only [decide_eq_true borrowed, Bool.not_true, decide_eq_false ordered]

/-- The actual entire low suffix and every other complementary coordinate are retained jointly. -/
lemma source_complement {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    (grouping (window state fits) (ArithmeticBlocks.remainderSource state)).2 =
      (grouping (window state fits) state).2 := by
  by_cases divisor : state.divisorLength ≠ 0
  · let selected := window state fits
    let subtracted := ArithmeticWindowProgram.step selected .subtractSigned state
    rw [source_eq state first second divisor fits]
    split
    · rw [step_complement]
      change (grouping selected subtracted).2 = _
      exact step_complement selected .subtractSigned state
    · change (grouping selected subtracted).2 = _
      exact step_complement selected .subtractSigned state
  · rw [source_finished state (Classical.not_not.mp divisor)]
    rfl

/-- The emitted native remainder program computes that same corrected physical upper word. -/
lemma native_target (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true) (zeroSign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    targetWord (window state fits) (ArithmeticBlocks.remainderStep width state) =
      SignedDivision.corrected (targetWord (window state fits) state)
        (sourceWord (window state fits) state) := by
  rw [ArithmeticBlocks.remainderStep_eq_source width state clean]
  exact source_target state first second zeroSign divisor fits

end

end QuantumAlg.MAU.Inversion.SharedEEA.RemainderBlockLaws
