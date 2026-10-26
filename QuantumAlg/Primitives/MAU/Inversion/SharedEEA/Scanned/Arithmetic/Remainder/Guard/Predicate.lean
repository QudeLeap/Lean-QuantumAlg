/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Specification
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Remainder
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Readout

/-!
# The actual remainder source guard survives its corresponding arithmetic

Signed subtraction may change Sign and therefore never reads it. Low
addition retains Sign and may safely read the original source test.
All complete natural metadata survive both original arithmetic modes.
These are semantic equalities, supplying no extra native instruction.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderGuard

noncomputable section

open EncodedBit

/-- The two actual remainder source positions use signed subtraction and low addition. -/
def operation (signed : Bool) : ArithmeticWindowProgram.Operation :=
  if signed then .subtractSigned else .addLow

/-- An enabled complete native guard certifies the untruncated natural window bound. -/
lemma enabled_admitted (width : Nat) (signed : Bool) (state : Data width)
    (enabled : ArithmeticGuard.remainderEnabled width signed state = true) :
    RemainderAddress.admitted width state.1 := by
  have positive := (Bool.and_eq_true_iff.mp enabled).1
  unfold RemainderAddress.admitted
  exact of_decide_eq_true positive

/-- Original Ctrl is not among the complete guard's predicate inputs. -/
lemma enabled_control_flip (width : Nat) (signed : Bool) (state : Data width) :
    ArithmeticGuard.remainderEnabled width signed ((ArithmeticGuard.flag width 4).flip state) =
      ArithmeticGuard.remainderEnabled width signed state := rfl

/-- The whole natural geometry and source-phase predicate survive their corresponding body. -/
lemma enabled_original (width : Nat) (signed : Bool)
    (selected : ArithmeticWindowRegisters.Window width) (state : Data width) :
    ArithmeticGuard.remainderEnabled width signed
        (ArithmeticAddress.liftSource width
          (ArithmeticWindowProgram.step selected (operation signed)) state) =
      ArithmeticGuard.remainderEnabled width signed state := by
  have retained := ArithmeticWindowPreservation.remainder_retained
    selected (operation signed) state.1
  have coefficient := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.1.1) retained
  have quotient := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.1.2) retained
  have divisor := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.1) retained
  have shift := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.2) retained
  have first := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.1) retained
  have second := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.2) retained
  change (ArithmeticWindowProgram.step selected (operation signed) state.1).coefficientLength =
    state.1.coefficientLength at coefficient
  change (ArithmeticWindowProgram.step selected (operation signed) state.1).quotientLength =
    state.1.quotientLength at quotient
  change (ArithmeticWindowProgram.step selected (operation signed) state.1).divisorLength =
    state.1.divisorLength at divisor
  change (ArithmeticWindowProgram.step selected (operation signed) state.1).shift =
    state.1.shift at shift
  change (ArithmeticWindowProgram.step selected (operation signed) state.1).flags.first =
    state.1.flags.first at first
  change (ArithmeticWindowProgram.step selected (operation signed) state.1).flags.second =
    state.1.flags.second at second
  cases signed with
  | false =>
      simp only [operation, Bool.false_eq_true, if_false] at coefficient quotient divisor
      simp only [operation, Bool.false_eq_true, if_false] at shift first second
      have sign := ArithmeticWindowPreservation.remainder_sign selected .addLow state.1 rfl
      simp only [ArithmeticGuard.remainderEnabled, ArithmeticGuard.condition,
        ArithmeticAddress.liftSource, operation, Bool.false_eq_true, if_false,
        coefficient, quotient, divisor, shift, first, second, sign]
  | true =>
      simp only [operation, if_true] at coefficient quotient divisor shift first second
      simp only [ArithmeticGuard.remainderEnabled, ArithmeticGuard.condition,
        ArithmeticAddress.liftSource, operation, if_true,
        coefficient, quotient, divisor, shift, first, second]

/-- Original full arithmetic commutes with toggling only its existing original Ctrl. -/
lemma original_control_flip (width : Nat) (signed : Bool)
    (selected : ArithmeticWindowRegisters.Window width) (state : Data width) :
    ArithmeticAddress.liftSource width (ArithmeticWindowProgram.step selected (operation signed))
        ((ArithmeticGuard.flag width 4).flip state) =
      (ArithmeticGuard.flag width 4).flip
        (ArithmeticAddress.liftSource width
          (ArithmeticWindowProgram.step selected (operation signed)) state) := by
  have actual := ArithmeticWindowPreservation.remainder_xorControl
    selected (operation signed) true state.1
  rw [NativePredicate.xorControl_true, NativePredicate.xorControl_true] at actual
  exact Prod.ext actual rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderGuard
