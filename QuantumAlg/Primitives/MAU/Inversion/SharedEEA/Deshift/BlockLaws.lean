/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.BlockLaws
import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Comparison

/-!
# Exact actual coefficient comparison in the deshift phase

Phase four executes the same native low subtraction, Sign complement, and
signed addition on the complete aligned coefficient region, whose right
boundary is the actual divisor length plus shift. Reading that divisor
boundary repairs the fixed-window loss of high integer coefficient bits
[LYL+26, sec_EEA/sub_regshare.tex:263-264,297-300;
sec_EEA/sub_opt.tex:61-66]. Every other field and every outside physical bit
is retained by the existing placed arithmetic and predicate cleanup.

These finite-word equations use the actual native coefficient block.
The original macro-state packing supplies the full-integer interpretation
and window bounds at its concrete phase-frame owner. No scalar callback,
caller-supplied fit certificate, or separate resource witness implements
an operation here.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DeshiftBlockLaws

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowProgram CoefficientWindowLaws

/-- The actual complete aligned coefficient region selected by the fourth-phase length readout. -/
def window {width : Nat} (state : Registers width)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) : Window width :=
  CoefficientWindowOrientation.coefficientWindow width
    (width + 3 - state.divisorLength.toNat - state.shift.toNat) (by omega)

private lemma source_subtract {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    ArithmeticInstruction.sourceStep .coefficientSubtract state =
      CoefficientWindowProgram.step (window state fits) .subtractLow state := by
  have physical := ArithmeticInstruction.sourceWindow_phaseFour
    .coefficientSubtract rfl state second fits
  have enabled : ArithmeticInstruction.sourceEnabled .coefficientSubtract state = true := by
    change (state.flags.first && (state.flags.second || !state.flags.sign)) = true
    rw [first, second]
    rfl
  rw [ArithmeticInstruction.sourceStep, enabled, physical]
  rfl

private lemma addition_window {width : Nat} (state : Registers width)
    (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    ArithmeticInstruction.sourceWindow .coefficientAdd (ArithmeticSign.coefficientStep
      (CoefficientWindowProgram.step (window state fits) .subtractLow state)) =
        some (window state fits) := by
  let current := CoefficientWindowProgram.step (window state fits) .subtractLow state
  have retained := ArithmeticWindowPreservation.coefficient_retained
    (window state fits) .subtractLow state
  have divisor : current.divisorLength = state.divisorLength :=
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.1) retained
  have shift : current.shift = state.shift :=
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.2) retained
  have secondSame : current.flags.second = true :=
    (congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.2)
      retained).trans second
  have currentFits : (ArithmeticSign.coefficientStep current).divisorLength.toNat +
      (ArithmeticSign.coefficientStep current).shift.toNat ≤ width + 3 := by
    change current.divisorLength.toNat + current.shift.toNat ≤ width + 3
    rw [divisor, shift]
    exact fits
  rw [ArithmeticInstruction.sourceWindow_phaseFour .coefficientAdd rfl
    (ArithmeticSign.coefficientStep current) secondSame currentFits]
  change some (CoefficientWindowOrientation.coefficientWindow width
    (width + 3 - current.divisorLength.toNat - current.shift.toNat) (by omega)) = _
  simp only [divisor, shift, window]

/-- Signed-word action is the comparison instruction on the complete physical operands. -/
lemma source_signed_word {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    signedTarget (window state fits) (ArithmeticBlocks.coefficientSource state) =
      NumberTheory.SharedEEA.SignedComparison.instruction
        (targetWord (window state fits) state) (sourceWord (window state fits) state)
        state.flags.sign := by
  let selected := window state fits
  let current := CoefficientWindowProgram.step selected .subtractLow state
  have retained := ArithmeticWindowPreservation.coefficient_retained selected .subtractLow state
  have firstSame : current.flags.first = true :=
    (congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.1)
      retained).trans first
  have signSame : current.flags.sign = state.flags.sign :=
    ArithmeticWindowPreservation.coefficient_sign selected .subtractLow state rfl
  rw [ArithmeticBlocks.coefficientSource, source_subtract state first second fits]
  rw [CoefficientBlockLaws.source_add selected (ArithmeticSign.coefficientStep current) firstSame
    (addition_window state second fits), step_signed_add]
  change BitVec.cons (current.flags.sign ^^ current.flags.first) (targetWord selected current) +
    (sourceWord selected current).setWidth (selected.length + 1) = _
  rw [signSame, firstSame, Bool.xor_true, step_low_subtract, step_sourceWord]
  rfl

/-- The actual weak comparison xors into Sign for arbitrary original Sign and complete operands. -/
lemma source_sign {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    (ArithmeticBlocks.coefficientSource state).flags.sign =
      (state.flags.sign ^^ decide ((sourceWord (window state fits) state).toNat ≤
        (targetWord (window state fits) state).toNat)) := by
  have signed := congrArg (fun word : BitVec ((window state fits).length + 1) => word.msb)
    (source_signed_word state first second fits)
  simpa only [signedTarget, BitVec.msb_cons,
    NumberTheory.SharedEEA.SignedComparison.instruction_sign] using signed

/-- The complete actual arithmetic target word is restored, including all selected high bits. -/
lemma source_target {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    targetWord (window state fits) (ArithmeticBlocks.coefficientSource state) =
      targetWord (window state fits) state := by
  have signed := congrArg
    (fun word : BitVec ((window state fits).length + 1) => word.setWidth (window state fits).length)
    (source_signed_word state first second fits)
  simpa only [signedTarget, BitVec.setWidth_cons,
    NumberTheory.SharedEEA.SignedComparison.instruction_low] using signed

/-- The actual source operand is unchanged through both arithmetic operations. -/
lemma source_source {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    sourceWord (window state fits) (ArithmeticBlocks.coefficientSource state) =
      sourceWord (window state fits) state := by
  let selected := window state fits
  let current := CoefficientWindowProgram.step selected .subtractLow state
  have firstSame : current.flags.first = true :=
    (congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.1)
      (ArithmeticWindowPreservation.coefficient_retained selected .subtractLow state)).trans first
  rw [ArithmeticBlocks.coefficientSource, source_subtract state first second fits]
  rw [CoefficientBlockLaws.source_add selected (ArithmeticSign.coefficientStep current) firstSame
    (addition_window state second fits), step_sourceWord]
  change sourceWord selected current = sourceWord selected state
  exact step_sourceWord selected .subtractLow state

/-- Every outside physical bit and every other retained field survives the real comparison. -/
lemma source_complement {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    (CoefficientWindowOrientation.grouping (window state fits)
      (ArithmeticBlocks.coefficientSource state)).2 =
      (CoefficientWindowOrientation.grouping (window state fits) state).2 := by
  let selected := window state fits
  let current := CoefficientWindowProgram.step selected .subtractLow state
  have firstSame : current.flags.first = true :=
    (congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.1)
      (ArithmeticWindowPreservation.coefficient_retained selected .subtractLow state)).trans first
  rw [ArithmeticBlocks.coefficientSource, source_subtract state first second fits]
  rw [CoefficientBlockLaws.source_add selected (ArithmeticSign.coefficientStep current) firstSame
    (addition_window state second fits), step_complement]
  change (CoefficientWindowOrientation.grouping selected current).2 = _
  exact step_complement selected .subtractLow state

private lemma eq_of_windows {width : Nat} (selected : Window width)
    (left right : Registers width)
    (source : sourceWord selected left = sourceWord selected right)
    (target : targetWord selected left = targetWord selected right)
    (sign : left.flags.sign = right.flags.sign)
    (other : (CoefficientWindowOrientation.grouping selected left).2 =
      (CoefficientWindowOrientation.grouping selected right).2) : left = right := by
  apply (CoefficientWindowOrientation.grouping selected).injective
  refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) other
  · apply Fin.ext
    rw [sourceWord_grouping, sourceWord_grouping] at source
    exact congrArg (fun word : BitVec selected.length => word.toNat) source
  · apply Fin.ext
    rw [targetWord_grouping, targetWord_grouping] at target
    exact congrArg (fun word : BitVec selected.length => word.toNat) target
  · exact sign

/-- The complete comparison changes only Sign and retains every original physical frame bit. -/
lemma source_frame {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    ArithmeticBlocks.coefficientSource state =
      { state with flags := { state.flags with sign :=
        (state.flags.sign ^^ decide ((sourceWord (window state fits) state).toNat ≤
          (targetWord (window state fits) state).toNat)) } } := by
  apply eq_of_windows (window state fits)
  · exact source_source state first second fits
  · exact source_target state first second fits
  · exact source_sign state first second fits
  · exact source_complement state first second fits

/-- The same emitted native program has the complete-frame comparison and restoration action. -/
lemma native_frame (width : Nat) (state : Registers width) (clean : state.control = false)
    (first : state.flags.first = true) (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    ArithmeticBlocks.coefficientStep width state =
      { state with flags := { state.flags with sign :=
        (state.flags.sign ^^ decide ((sourceWord (window state fits) state).toNat ≤
          (targetWord (window state fits) state).toNat)) } } := by
  rw [ArithmeticBlocks.coefficientStep_eq_source width state clean]
  exact source_frame state first second fits

/-- The same emitted coefficient program implements the complete-word Sign comparison. -/
lemma native_sign (width : Nat) (state : Registers width) (clean : state.control = false)
    (first : state.flags.first = true) (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    (ArithmeticBlocks.coefficientStep width state).flags.sign =
      (state.flags.sign ^^ decide ((sourceWord (window state fits) state).toNat ≤
        (targetWord (window state fits) state).toNat)) := by
  rw [ArithmeticBlocks.coefficientStep_eq_source width state clean]
  exact source_sign state first second fits

end

end QuantumAlg.MAU.Inversion.SharedEEA.DeshiftBlockLaws
