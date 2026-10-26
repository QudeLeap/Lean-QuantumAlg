/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Guard.Action
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Window.Empty
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Instruction

/-!
# Complete original remainder boundaries, including terminal and empty regions

The same source phase and nonzero-divisor tests are retained. The
original region permits length zero; its actual empty native word is
the identity. Rejecting that boundary in the positive-window traversal
therefore changes no original full-frame result on any finite label.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderGuard

noncomputable section

open EncodedBit

/-- The two public choices are exactly the corresponding original remainder source instructions. -/
def instruction (signed : Bool) : ArithmeticInstruction.Instruction :=
  if signed then .remainderSubtract else .remainderAddback

private def region (width : Nat) (state : Registers width) :
    Option (ArithmeticWindowRegisters.Window width) :=
  if fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3 then
    some (ArithmeticWindowRegisters.remainderWindow width
      (state.coefficientLength.toNat + state.quotientLength.toNat + 1) state.shift.toNat fits)
  else none

/-- The original current-field source window uses exactly the same complete remainder geometry. -/
lemma original_sourceWindow (width : Nat) (signed : Bool) (state : Registers width) :
    ArithmeticInstruction.sourceWindow (instruction signed) state = region width state := by
  cases signed <;> rfl

/-- Every admitted positive geometry selects exactly the same physical source region. -/
lemma original_region_of_admitted (width : Nat) (state : Registers width)
    (accepted : RemainderAddress.admitted width state) :
    region width state = some (RemainderAddress.window width state accepted) := by
  have bound : state.coefficientLength.toNat + state.quotientLength.toNat + 1 +
      state.shift.toNat ≤ width + 3 := accepted.le
  rw [region, dif_pos bound]
  rfl

/-- Rejected complete metadata are absent or select an actual identity empty arithmetic word. -/
lemma original_region_of_rejected (width : Nat) (operation : ArithmeticWindowProgram.Operation)
    (state : Registers width) (rejected : ¬RemainderAddress.admitted width state) :
    (match region width state with
      | some selected => ArithmeticWindowProgram.step selected operation state
      | none => state) = state := by
  by_cases bound : state.coefficientLength.toNat + state.quotientLength.toNat + 1 +
      state.shift.toNat ≤ width + 3
  · have empty : width + 3 - (state.coefficientLength.toNat + state.quotientLength.toNat + 1) -
        state.shift.toNat = 0 := by
      unfold RemainderAddress.admitted at rejected
      omega
    rw [region, dif_pos bound]
    exact ArithmeticEmptyWindow.remainderStep_empty _ empty operation state
  · rw [region, dif_neg bound]

/-- Original remainder phase and the full nonzero-divisor condition are unchanged. -/
lemma original_sourceEnabled (width : Nat) (signed : Bool) (state : Data width) :
    ArithmeticInstruction.sourceEnabled (instruction signed) state.1 =
      ArithmeticGuard.condition width signed false state := by
  cases signed <;> rfl

private lemma original_body (signed : Bool) {width : Nat}
    (selected : ArithmeticWindowRegisters.Window width) (state : Registers width) :
    ArithmeticSelector.bodyStep selected (ArithmeticInstruction.operation (instruction signed))
        (ArithmeticInstruction.coefficient (instruction signed)) state =
      ArithmeticWindowProgram.step selected (operation signed) state := by
  cases signed <;> rfl

/-- The full independent result is the exact original source instruction at every finite label. -/
lemma step_eq_original (width : Nat) (signed : Bool) (state : Data width) :
    step width signed state =
      ArithmeticAddress.liftSource width (ArithmeticInstruction.sourceStep (instruction signed))
        state := by
  by_cases accepted : RemainderAddress.admitted width state.1
  · have guardEq : ArithmeticGuard.remainderEnabled width signed state =
        ArithmeticGuard.condition width signed false state := by
      have positive : state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1 +
          state.1.shift.toNat < width + 3 := accepted
      unfold ArithmeticGuard.remainderEnabled
      rw [decide_eq_true positive, Bool.true_and]
    by_cases phase : ArithmeticGuard.condition width signed false state = true
    · have active := guardEq.trans phase
      rw [step, dif_pos active]
      unfold ArithmeticAddress.liftSource ArithmeticInstruction.sourceStep
      rw [original_sourceEnabled width signed state, if_pos phase,
        original_sourceWindow, original_region_of_admitted width state.1 accepted]
      simp only [original_body]
    · have inactive : ArithmeticGuard.remainderEnabled width signed state ≠ true := by
        rw [guardEq]
        exact phase
      rw [step, dif_neg inactive]
      unfold ArithmeticAddress.liftSource ArithmeticInstruction.sourceStep
      rw [original_sourceEnabled width signed state, if_neg phase]
  · have inactive : ArithmeticGuard.remainderEnabled width signed state ≠ true := by
      intro active
      exact accepted (enabled_admitted width signed state active)
    rw [step, dif_neg inactive]
    unfold ArithmeticAddress.liftSource ArithmeticInstruction.sourceStep
    rw [original_sourceEnabled width signed state]
    split
    · rw [original_sourceWindow]
      have identity := original_region_of_rejected width (operation signed) state.1 accepted
      cases selectedRegion : region width state.1 with
      | none => rfl
      | some selected =>
          simp only [original_body]
          rw [selectedRegion] at identity
          change ArithmeticWindowProgram.step selected (operation signed) state.1 = state.1
            at identity
          rw [identity]
    · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderGuard
