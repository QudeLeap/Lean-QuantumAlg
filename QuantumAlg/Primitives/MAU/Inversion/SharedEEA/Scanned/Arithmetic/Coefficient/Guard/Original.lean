/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Guard.Action
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Window.Empty
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Instruction

/-!
# Complete original coefficient-window boundaries, including rejected empty windows

The original phase-four region admits length zero at its boundary.
The actual zero-width native word has already been proved to retain
the full original frame, so rejecting that boundary changes no result.
All complete finite metadata remain covered by these identities.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientGuard

noncomputable section

open EncodedBit

/-- The two public coefficient choices name precisely their original source instructions. -/
def instruction (signed : Bool) : ArithmeticInstruction.Instruction :=
  if signed then .coefficientAdd else .coefficientSubtract

/-- An admitted positive complete geometry selects exactly the original physical region. -/
lemma original_region_of_admitted (width : Nat) (state : Registers width)
    (accepted : CoefficientAddress.admitted width state) :
    ArithmeticInstruction.coefficientRegion width state.coefficientLength.toNat
        state.divisorLength.toNat state.shift.toNat state.flags.second =
      some (CoefficientCoordinates.window width (CoefficientAddress.wordLength width state)
        (CoefficientAddress.wordLength_fits width state accepted)) := by
  unfold CoefficientAddress.admitted at accepted
  cases second : state.flags.second with
  | false =>
      simp only [second, Bool.false_eq_true, if_false] at accepted
      simp only [ArithmeticInstruction.coefficientRegion, CoefficientAddress.wordLength,
        second, Bool.false_eq_true, if_false, dif_pos accepted]
      rfl
  | true =>
      simp only [second, if_true] at accepted
      have fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3 := by omega
      simp only [ArithmeticInstruction.coefficientRegion, CoefficientAddress.wordLength,
        second, if_true, dif_pos fits]
      rfl

/-- A rejected full finite geometry is either absent or an actual identity zero-width region. -/
lemma original_region_of_rejected (width : Nat) (operation : ArithmeticWindowProgram.Operation)
    (state : Registers width) (rejected : ¬CoefficientAddress.admitted width state) :
    (match ArithmeticInstruction.coefficientRegion width state.coefficientLength.toNat
        state.divisorLength.toNat state.shift.toNat state.flags.second with
      | some selected => CoefficientWindowProgram.step selected operation state
      | none => state) = state := by
  unfold CoefficientAddress.admitted at rejected
  cases second : state.flags.second with
  | false =>
      simp only [second, Bool.false_eq_true, if_false] at rejected
      simp only [ArithmeticInstruction.coefficientRegion, Bool.false_eq_true,
        if_false, dif_neg rejected]
  | true =>
      simp only [second, if_true] at rejected
      by_cases fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3
      · have empty : width + 3 - state.divisorLength.toNat - state.shift.toNat = 0 := by omega
        simp only [ArithmeticInstruction.coefficientRegion, if_true, dif_pos fits]
        exact ArithmeticEmptyWindow.coefficientStep_empty _ empty operation state
      · simp only [ArithmeticInstruction.coefficientRegion, if_true, dif_neg fits]

/-- The original source condition reads exactly the same complete actual phase bits. -/
lemma original_sourceEnabled (width : Nat) (signed : Bool) (state : Data width) :
    ArithmeticInstruction.sourceEnabled (instruction signed) state.1 =
      ArithmeticGuard.condition width signed true state := by
  cases signed <;> rfl

/-- Both original coefficient source choices use the same phase-dependent complete region. -/
lemma original_sourceWindow (width : Nat) (signed : Bool) (state : Registers width) :
    ArithmeticInstruction.sourceWindow (instruction signed) state =
      ArithmeticInstruction.coefficientRegion width state.coefficientLength.toNat
        state.divisorLength.toNat state.shift.toNat state.flags.second := by
  cases signed <;> rfl

private lemma original_body (signed : Bool) {width : Nat}
    (selected : ArithmeticWindowRegisters.Window width) (state : Registers width) :
    ArithmeticSelector.bodyStep selected (ArithmeticInstruction.operation (instruction signed))
        (ArithmeticInstruction.coefficient (instruction signed)) state =
      CoefficientWindowProgram.step selected (operation signed) state := by
  cases signed <;> rfl

/-- The independent complete result is exactly the original source instruction at every label. -/
lemma step_eq_original (width : Nat) (signed : Bool) (state : Data width) :
    step width signed state =
      ArithmeticAddress.liftSource width (ArithmeticInstruction.sourceStep (instruction signed))
        state := by
  by_cases accepted : CoefficientAddress.admitted width state.1
  · have guardEq : ArithmeticGuard.coefficientEnabled width signed state =
        ArithmeticGuard.condition width signed true state := by
      have positive : if state.1.flags.second then
          state.1.divisorLength.toNat + state.1.shift.toNat < width + 3
        else state.1.coefficientLength.toNat + 1 ≤ width + 3 := accepted
      unfold ArithmeticGuard.coefficientEnabled
      rw [decide_eq_true positive, Bool.true_and]
    by_cases phase : ArithmeticGuard.condition width signed true state = true
    · have active := guardEq.trans phase
      rw [step, dif_pos active]
      unfold ArithmeticAddress.liftSource ArithmeticInstruction.sourceStep
      rw [original_sourceEnabled width signed state, if_pos phase,
        original_sourceWindow, original_region_of_admitted width state.1 accepted]
      simp only [original_body]
    · have inactive : ArithmeticGuard.coefficientEnabled width signed state ≠ true := by
        rw [guardEq]
        exact phase
      rw [step, dif_neg inactive]
      unfold ArithmeticAddress.liftSource ArithmeticInstruction.sourceStep
      rw [original_sourceEnabled width signed state, if_neg phase]
  · have inactive : ArithmeticGuard.coefficientEnabled width signed state ≠ true := by
      intro active
      exact accepted (enabled_admitted width signed state active)
    rw [step, dif_neg inactive]
    unfold ArithmeticAddress.liftSource ArithmeticInstruction.sourceStep
    rw [original_sourceEnabled width signed state]
    split
    · rw [original_sourceWindow]
      have identity := original_region_of_rejected width (operation signed) state.1 accepted
      cases region : ArithmeticInstruction.coefficientRegion width state.1.coefficientLength.toNat
          state.1.divisorLength.toNat state.1.shift.toNat state.1.flags.second with
      | none => rfl
      | some selected =>
          simp only [original_body]
          rw [region] at identity
          change CoefficientWindowProgram.step selected (operation signed) state.1 =
            state.1 at identity
          rw [identity]
    · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientGuard
