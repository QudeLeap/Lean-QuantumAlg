/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Blocks
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Laws
import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Coefficient

/-!
# Actual phase-three coefficient block and the signed coefficient word

The actual phase-three source block conditionally subtracts from the
integer window, complements Sign, and adds into Sign and the same window
[LYL+26, sec_EEA/sub_regshare.tex:288-296;
LYL+26, sec_EEA/sub_opt.tex:61-66]. This owner connects that existing
complete native coefficient program to `SignedCoefficient.addBit`, using
its actual current coefficient-length field to select the physical region.

The exact equation permits arbitrary quotient digit, complementary bits,
and incoming Ctrl at the source-operation level. Native refinement uses
the algorithm's internal Ctrl-zero invariant. Physical fit and the phase
bits are local reachable-frame obligations, not new original input-domain
assumptions. The arithmetic equation itself needs neither an integer-part
inequality nor an unproved addition bound; those capacity invariants are
used separately to infer Sign cleanup on the reachable Euclidean path.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientBlockLaws

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowProgram
open CoefficientWindowLaws

private lemma arithmetic_fields {width : Nat} (window : Window width) (operation : Operation)
    (state : Registers width) :
    (CoefficientWindowProgram.step window operation state).coefficientLength =
        state.coefficientLength ∧
      (CoefficientWindowProgram.step window operation state).flags.first = state.flags.first := by
  have actual := ArithmeticWindowPreservation.coefficient_retained window operation state
  exact ⟨congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.1.1) actual,
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.1) actual⟩

private lemma source_subtract {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    ArithmeticInstruction.sourceStep .coefficientSubtract state =
      if state.flags.sign then state else
        CoefficientWindowProgram.step
          (CoefficientWindowOrientation.coefficientWindow width
            (state.coefficientLength.toNat + 1) fits) .subtractLow state := by
  have physical : ArithmeticInstruction.sourceWindow .coefficientSubtract state =
      some (CoefficientWindowOrientation.coefficientWindow width
        (state.coefficientLength.toNat + 1) fits) :=
    ArithmeticInstruction.sourceWindow_phaseThree .coefficientSubtract rfl state second fits
  have enabled : ArithmeticInstruction.sourceEnabled .coefficientSubtract state =
      !state.flags.sign := by
    change (state.flags.first && (state.flags.second || !state.flags.sign)) = _
    rw [first, second]
    rfl
  rw [ArithmeticInstruction.sourceStep, enabled, physical]
  cases digit : state.flags.sign <;> rfl

private lemma source_add {width : Nat} (window : Window width) (state : Registers width)
    (first : state.flags.first = true)
    (physical : ArithmeticInstruction.sourceWindow .coefficientAdd state = some window) :
    ArithmeticInstruction.sourceStep .coefficientAdd state =
      CoefficientWindowProgram.step window .addSigned state := by
  change (if state.flags.first then
    match ArithmeticInstruction.sourceWindow .coefficientAdd state with
    | some selected => ArithmeticSelector.bodyStep selected .addSigned true state
    | none => state
    else state) = _
  rw [first, physical]
  rfl

private lemma subtraction_fields {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    let current := ArithmeticInstruction.sourceStep .coefficientSubtract state
    current.coefficientLength = state.coefficientLength ∧ current.flags.first = true ∧
      current.flags.sign = state.flags.sign := by
  dsimp only
  rw [source_subtract state first second fits]
  split
  · exact ⟨rfl, first, rfl⟩
  · let window := CoefficientWindowOrientation.coefficientWindow width
      (state.coefficientLength.toNat + 1) fits
    have fields := arithmetic_fields window .subtractLow state
    exact ⟨fields.1, fields.2.trans first,
      ArithmeticWindowPreservation.coefficient_sign window .subtractLow state rfl⟩

private lemma subtraction_second {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    (ArithmeticInstruction.sourceStep .coefficientSubtract state).flags.second = false := by
  rw [source_subtract state first second fits]
  split
  · exact second
  · let window := CoefficientWindowOrientation.coefficientWindow width
      (state.coefficientLength.toNat + 1) fits
    exact (congrArg
      (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.2)
      (ArithmeticWindowPreservation.coefficient_retained window .subtractLow state)).trans second

private lemma addition_window {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    ArithmeticInstruction.sourceWindow .coefficientAdd
      (ArithmeticSign.coefficientStep
        (ArithmeticInstruction.sourceStep .coefficientSubtract state)) =
      some (CoefficientWindowOrientation.coefficientWindow width
        (state.coefficientLength.toNat + 1) fits) := by
  let current := ArithmeticInstruction.sourceStep .coefficientSubtract state
  have fields := subtraction_fields state first second fits
  have currentSecond : (ArithmeticSign.coefficientStep current).flags.second = false :=
    subtraction_second state first second fits
  have currentFits : (ArithmeticSign.coefficientStep current).coefficientLength.toNat + 1 ≤
      width + 3 := by
    change current.coefficientLength.toNat + 1 ≤ width + 3
    rw [fields.1]
    exact fits
  rw [ArithmeticInstruction.sourceWindow_phaseThree .coefficientAdd rfl
    (ArithmeticSign.coefficientStep current) currentSecond currentFits]
  have plainFits : current.coefficientLength.toNat + 1 ≤ width + 3 := currentFits
  change some (CoefficientWindowOrientation.coefficientWindow width
    (current.coefficientLength.toNat + 1) plainFits) = _
  have sameWindow (left right : Nat) (leftFits : left ≤ width + 3)
      (rightFits : right ≤ width + 3) (same : left = right) :
      CoefficientWindowOrientation.coefficientWindow width left leftFits =
        CoefficientWindowOrientation.coefficientWindow width right rightFits := by
    cases same
    rfl
  exact congrArg some (sameWindow _ _ plainFits fits
    (congrArg (fun word : BitVec width.size => word.toNat + 1) fields.1))

/-- Actual source operations equal the exact signed coefficient instruction for either digit. -/
lemma source_signed_word {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    let window := CoefficientWindowOrientation.coefficientWindow width
      (state.coefficientLength.toNat + 1) fits
    signedTarget window (ArithmeticBlocks.coefficientSource state) =
      NumberTheory.SharedEEA.SignedCoefficient.addBit
        (targetWord window state) (sourceWord window state) state.flags.sign := by
  dsimp only
  let window := CoefficientWindowOrientation.coefficientWindow width
    (state.coefficientLength.toNat + 1) fits
  let current := ArithmeticInstruction.sourceStep .coefficientSubtract state
  have fields := subtraction_fields state first second fits
  have currentSource : sourceWord window current = sourceWord window state := by
    dsimp only [current]
    rw [source_subtract state first second fits]
    split
    · rfl
    · exact step_sourceWord window .subtractLow state
  have currentTarget : targetWord window current =
      if state.flags.sign then targetWord window state
      else targetWord window state - sourceWord window state := by
    dsimp only [current]
    rw [source_subtract state first second fits]
    split
    · rfl
    · exact step_low_subtract window state
  change signedTarget window (ArithmeticInstruction.sourceStep .coefficientAdd
    (ArithmeticSign.coefficientStep current)) = _
  rw [source_add window (ArithmeticSign.coefficientStep current) fields.2.1
    (addition_window state first second fits), step_signed_add]
  change BitVec.cons (current.flags.sign ^^ current.flags.first) (targetWord window current) +
    (sourceWord window current).setWidth (window.length + 1) = _
  rw [fields.2.2, fields.2.1, Bool.xor_true, currentTarget, currentSource]
  rfl

/-- The same actual block keeps every original outside coordinate, including fractional bits. -/
lemma source_complement {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    let window := CoefficientWindowOrientation.coefficientWindow width
      (state.coefficientLength.toNat + 1) fits
    (CoefficientWindowOrientation.grouping window (ArithmeticBlocks.coefficientSource state)).2 =
      (CoefficientWindowOrientation.grouping window state).2 := by
  dsimp only
  let window := CoefficientWindowOrientation.coefficientWindow width
    (state.coefficientLength.toNat + 1) fits
  let current := ArithmeticInstruction.sourceStep .coefficientSubtract state
  have fields := subtraction_fields state first second fits
  change (CoefficientWindowOrientation.grouping window
    (ArithmeticInstruction.sourceStep .coefficientAdd
      (ArithmeticSign.coefficientStep current))).2 = _
  rw [source_add window (ArithmeticSign.coefficientStep current) fields.2.1
    (addition_window state first second fits), step_complement]
  change (CoefficientWindowOrientation.grouping window current).2 = _
  dsimp only [current]
  rw [source_subtract state first second fits]
  split
  · rfl
  · exact step_complement window .subtractLow state

/-- The complete emitted coefficient program has that same actual signed-word result. -/
lemma native_signed_word (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true)
    (second : state.flags.second = false) (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    let window := CoefficientWindowOrientation.coefficientWindow width
      (state.coefficientLength.toNat + 1) fits
    signedTarget window (ArithmeticBlocks.coefficientStep width state) =
      NumberTheory.SharedEEA.SignedCoefficient.addBit
        (targetWord window state) (sourceWord window state) state.flags.sign := by
  rw [ArithmeticBlocks.coefficientStep_eq_source width state clean]
  exact source_signed_word state first second fits

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientBlockLaws
