/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Selection.Key
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Program

/-!
# Exact selector-field preservation by the actual arithmetic windows

Every existing TTK window operation retains all four finite length fields,
both phase bits, arbitrary Iter, and Ctrl. Low operations also retain Sign.
The signed operations omit Sign from the actual equality readout because
they update it [LYL+26, sec_EEA/sub_opt.tex:43-48,61-66]. These facts justify
uncomputing that same equality after the selected native arithmetic.

The statements concern the complete frame actions already realized by the
actual placed programs. No separate execution rule or clean-work condition
is introduced, and the outside portions of both words remain in the proved
complete grouping.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowPreservation

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowProgram ArithmeticSelectionKey

/-- Sign is read only for a low operation, whose existing arithmetic retains it. -/
def readsSign : Operation → Bool
  | .addLow | .subtractLow => true
  | .addSigned | .subtractSigned => false

private abbrev Retained (width : Nat) :=
  (BitVec width.size × BitVec width.size) ×
    ((BitVec width.size × BitVec width.size) × ((Bool × Bool) × (Bool × Bool)))

private def retained {width : Nat} (state : Registers width) : Retained width :=
  ((state.coefficientLength, state.quotientLength),
    ((state.divisorLength, state.shift),
      ((state.flags.first, state.flags.second), (state.flags.iteration, state.control))))

private lemma remainder_retained {width : Nat} (window : Window width)
    (operation : Operation) (state : Registers width) :
    retained (ArithmeticWindowProgram.step window operation state) = retained state :=
  congrArg (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window =>
    pair.2.2.2) (ArithmeticWindowProgram.step_grouping window operation state)

private lemma coefficient_retained {width : Nat} (window : Window width)
    (operation : Operation) (state : Registers width) :
    retained (CoefficientWindowProgram.step window operation state) = retained state :=
  congrArg (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window =>
    pair.2.2.2) (CoefficientWindowProgram.step_grouping window operation state)

private lemma focus_sign {length : Nat} (operation : Operation)
    (state : Addition.TTK.OverflowRegisters length) (low : readsSign operation = true) :
    (focusStep operation state).2 = state.2 := by
  cases operation <;> simp only [readsSign, Bool.false_eq_true] at low
  all_goals rfl

private lemma remainder_sign {width : Nat} (window : Window width)
    (operation : Operation) (state : Registers width) (low : readsSign operation = true) :
    (ArithmeticWindowProgram.step window operation state).flags.sign = state.flags.sign := by
  have same := congrArg
    (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window => pair.1.2)
    (ArithmeticWindowProgram.step_grouping window operation state)
  exact same.trans (focus_sign operation (grouping window state).1 low)

private lemma coefficient_sign {width : Nat} (window : Window width)
    (operation : Operation) (state : Registers width) (low : readsSign operation = true) :
    (CoefficientWindowProgram.step window operation state).flags.sign = state.flags.sign := by
  have same := congrArg
    (fun pair : Addition.TTK.OverflowRegisters window.length × Complement window => pair.1.2)
    (CoefficientWindowProgram.step_grouping window operation state)
  exact same.trans
    (focus_sign operation (CoefficientWindowOrientation.grouping window state).1 low)

private lemma readKey_eq_of_retained {width : Nat} (includeSign : Bool)
    (before after : Registers width) (same : retained after = retained before)
    (signSame : includeSign = true → after.flags.sign = before.flags.sign) :
    readKey width includeSign after = readKey width includeSign before := by
  have coefficient := congrArg (fun value : Retained width => value.1.1) same
  have quotient := congrArg (fun value : Retained width => value.1.2) same
  have divisor := congrArg (fun value : Retained width => value.2.1.1) same
  have shift := congrArg (fun value : Retained width => value.2.1.2) same
  have first := congrArg (fun value : Retained width => value.2.2.1.1) same
  have second := congrArg (fun value : Retained width => value.2.2.1.2) same
  change after.coefficientLength = before.coefficientLength at coefficient
  change after.quotientLength = before.quotientLength at quotient
  change after.divisorLength = before.divisorLength at divisor
  change after.shift = before.shift at shift
  change after.flags.first = before.flags.first at first
  change after.flags.second = before.flags.second at second
  funext index
  change (ArithmeticSelectionLayout.sourceBit width includeSign index).get after =
    (ArithmeticSelectionLayout.sourceBit width includeSign index).get before
  rw [ArithmeticSelectionLayout.sourceBit_get, ArithmeticSelectionLayout.sourceBit_get,
    coefficient, quotient, divisor, shift, first, second]
  cases includeSign with
  | true => rw [signSame rfl]
  | false =>
      have within := index.isLt
      change index.val < 4 * width.size + 2 + 0 at within
      split_ifs <;> first | rfl | omega

/-- All actual sources of the appropriate remainder predicate survive the complete native body. -/
lemma remainder_readKey {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    readKey width (readsSign operation) (ArithmeticWindowProgram.step window operation state) =
      readKey width (readsSign operation) state :=
  readKey_eq_of_retained (readsSign operation) state _
    (remainder_retained window operation state) (remainder_sign window operation state)

/-- The little-endian coefficient body retains every source bit used for its own equality. -/
lemma coefficient_readKey {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    readKey width (readsSign operation) (CoefficientWindowProgram.step window operation state) =
      readKey width (readsSign operation) state :=
  readKey_eq_of_retained (readsSign operation) state _
    (coefficient_retained window operation state) (coefficient_sign window operation state)

/-- The actual ungated remainder body retains arbitrary incoming Ctrl. -/
lemma remainder_control {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    (ArithmeticWindowProgram.step window operation state).control = state.control :=
  congrArg (fun value : Retained width => value.2.2.2.2)
    (remainder_retained window operation state)

/-- The actual ungated coefficient body retains arbitrary incoming Ctrl. -/
lemma coefficient_control {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    (CoefficientWindowProgram.step window operation state).control = state.control :=
  congrArg (fun value : Retained width => value.2.2.2.2)
    (coefficient_retained window operation state)

/-- The complete remainder action restores arbitrary Iter, not only its zero basis value. -/
lemma remainder_iteration {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    (ArithmeticWindowProgram.step window operation state).flags.iteration = state.flags.iteration :=
  congrArg (fun value : Retained width => value.2.2.2.1)
    (remainder_retained window operation state)

/-- The coefficient action likewise retains the entire original arbitrary Iter bit. -/
lemma coefficient_iteration {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    (CoefficientWindowProgram.step window operation state).flags.iteration =
      state.flags.iteration :=
  congrArg (fun value : Retained width => value.2.2.2.1)
    (coefficient_retained window operation state)

/-- Changing only Ctrl commutes with the ungated remainder arithmetic on the complete frame. -/
lemma remainder_xorControl {width : Nat} (window : Window width) (operation : Operation)
    (value : Bool) (state : Registers width) :
    ArithmeticWindowProgram.step window operation (NativePredicate.xorControl value state) =
      NativePredicate.xorControl value (ArithmeticWindowProgram.step window operation state) := by
  simp only [ArithmeticWindowProgram.step, ArithmeticWindowPlacement.placedStep_eq]
  rfl

/-- The same exact complete-frame commutation holds in the coefficient orientation. -/
lemma coefficient_xorControl {width : Nat} (window : Window width) (operation : Operation)
    (value : Bool) (state : Registers width) :
    CoefficientWindowProgram.step window operation (NativePredicate.xorControl value state) =
      NativePredicate.xorControl value (CoefficientWindowProgram.step window operation state) := by
  simp only [CoefficientWindowProgram.step, EncodedBit.FullPlacement.step,
    CoefficientWindowProgram.placement_grouping_equiv]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowPreservation
