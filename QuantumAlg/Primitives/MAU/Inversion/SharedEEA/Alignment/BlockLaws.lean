/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.BlockLaws

/-!
# Actual signed subtraction and unconditional add-back in alignment

With both phase bits zero, the source executes signed remainder subtraction,
does not complement Sign, and unconditionally adds the low operand back
[LYL+26, sec_EEA/sub_opt.tex:37-48]. The whole original target word is
restored and Sign records strict underflow, including the equality boundary.

The equations below concern these actual native lists and all original
register bits. The old Sign-zero and physical-window bounds are local
reachable-frame obligations. The alignment trajectory must derive them
from the original Euclidean input; they are not new caller conditions.
Interpreting the physical high-window comparison at its actual binary
scale is separate from this finite-word native arithmetic law.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AlignmentBlockLaws

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowProgram ArithmeticWindowLaws

private theorem source_addback {width : Nat} (selected : Window width) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = false)
    (divisor : state.divisorLength ≠ 0)
    (physical : ArithmeticInstruction.sourceWindow .remainderAddback state = some selected) :
    ArithmeticInstruction.sourceStep .remainderAddback state =
      ArithmeticWindowProgram.step selected .addLow state := by
  have enabled : ArithmeticInstruction.sourceEnabled .remainderAddback state = true := by
    rw [ArithmeticInstruction.sourceEnabled_active .remainderAddback state divisor]
    change (!state.flags.first && (!state.flags.second || !state.flags.sign)) = true
    rw [first, second]
    rfl
  rw [ArithmeticInstruction.sourceStep, enabled, physical]
  rfl

/-- Actual phase-zero source order is signed subtraction followed by unconditional low addition. -/
theorem source_eq {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    let selected := RemainderBlockLaws.window state fits
    ArithmeticBlocks.remainderSource state =
      ArithmeticWindowProgram.step selected .addLow
        (ArithmeticWindowProgram.step selected .subtractSigned state) := by
  dsimp only
  let selected := RemainderBlockLaws.window state fits
  let subtracted := ArithmeticWindowProgram.step selected .subtractSigned state
  have physical : ArithmeticInstruction.sourceWindow .remainderSubtract state = some selected := by
    change (if bound : state.coefficientLength.toNat + state.quotientLength.toNat + 1 +
        state.shift.toNat ≤ width + 3 then
      some (remainderWindow width
        (state.coefficientLength.toNat + state.quotientLength.toNat + 1) state.shift.toNat bound)
      else none) = _
    rw [dif_pos fits]
    rfl
  have retained := ArithmeticWindowPreservation.remainder_retained selected .subtractSigned state
  have coefficient : subtracted.coefficientLength = state.coefficientLength :=
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.1.1) retained
  have quotient : subtracted.quotientLength = state.quotientLength :=
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.1.2) retained
  have shift : subtracted.shift = state.shift :=
    congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.2) retained
  have subtractedDivisor : subtracted.divisorLength ≠ 0 := by
    have same : subtracted.divisorLength = state.divisorLength :=
      congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.1) retained
    exact fun zero => divisor (same.symm.trans zero)
  have firstSame : subtracted.flags.first = false :=
    (congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.1)
      retained).trans first
  have secondSame : subtracted.flags.second = false :=
    (congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.2)
      retained).trans second
  have marked : ArithmeticSign.remainderStep subtracted = subtracted := by
    have same : (subtracted.flags.sign ^^ (!subtracted.flags.first && subtracted.flags.second)) =
        subtracted.flags.sign := by
      rw [secondSame, Bool.and_false, Bool.xor_false]
    unfold ArithmeticSign.remainderStep
    rw [same]
  have addWindow : ArithmeticInstruction.sourceWindow .remainderAddback subtracted =
      some selected := by
    change (if bound : subtracted.coefficientLength.toNat + subtracted.quotientLength.toNat + 1 +
        subtracted.shift.toNat ≤ width + 3 then
      some (remainderWindow width
        (subtracted.coefficientLength.toNat + subtracted.quotientLength.toNat + 1)
        subtracted.shift.toNat bound) else none) = _
    rw [coefficient, quotient, shift, dif_pos fits]
    rfl
  rw [ArithmeticBlocks.remainderSource,
    RemainderBlockLaws.source_subtract selected state first divisor physical, marked,
    source_addback selected subtracted firstSame secondSame subtractedDivisor addWindow]

private theorem eq_of_windows {width : Nat} (selected : Window width)
    (left right : Registers width)
    (source : sourceWord selected left = sourceWord selected right)
    (target : targetWord selected left = targetWord selected right)
    (sign : left.flags.sign = right.flags.sign)
    (other : (grouping selected left).2 = (grouping selected right).2) : left = right := by
  apply (grouping selected).injective
  refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) other
  · apply Fin.ext
    rw [sourceWord_grouping, sourceWord_grouping] at source
    exact congrArg (fun word : BitVec selected.length => word.toNat) source
  · apply Fin.ext
    rw [targetWord_grouping, targetWord_grouping] at target
    exact congrArg (fun word : BitVec selected.length => word.toNat) target
  · exact sign

/-- Actual subtraction and add-back restore the complete frame and retain strict borrow in Sign. -/
theorem source_frame {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = false)
    (zeroSign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    ArithmeticBlocks.remainderSource state =
      { state with flags := { state.flags with sign := (decide
        ((targetWord (RemainderBlockLaws.window state fits) state).toNat <
          (sourceWord (RemainderBlockLaws.window state fits) state).toNat)) } } := by
  let selected := RemainderBlockLaws.window state fits
  rw [source_eq state first second divisor fits]
  apply eq_of_windows selected
  · exact (step_sourceWord selected .addLow _).trans
      (step_sourceWord selected .subtractSigned state)
  · change targetWord selected (ArithmeticWindowProgram.step selected .addLow
      (ArithmeticWindowProgram.step selected .subtractSigned state)) = targetWord selected state
    rw [step_low_add, step_subtract_low selected state zeroSign,
      step_sourceWord, BitVec.sub_add_cancel]
  · exact (ArithmeticWindowPreservation.remainder_sign selected .addLow _ rfl).trans
      (step_subtract_sign selected state zeroSign)
  · exact (step_complement selected .addLow _).trans
      (step_complement selected .subtractSigned state)

/-- The same emitted native remainder program implements full restoration and the alignment test. -/
theorem native_frame (width : Nat) (state : Registers width) (clean : state.control = false)
    (first : state.flags.first = false) (second : state.flags.second = false)
    (zeroSign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ 0)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    ArithmeticBlocks.remainderStep width state =
      { state with flags := { state.flags with sign := (decide
        ((targetWord (RemainderBlockLaws.window state fits) state).toNat <
          (sourceWord (RemainderBlockLaws.window state fits) state).toNat)) } } := by
  rw [ArithmeticBlocks.remainderStep_eq_source width state clean]
  exact source_frame state first second zeroSign divisor fits

end

end QuantumAlg.MAU.Inversion.SharedEEA.AlignmentBlockLaws
