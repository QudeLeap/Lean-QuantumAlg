/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Alignment.BlockLaws
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Macro.Boundary
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Phase.Frame
import all QuantumAlg.Util.NumberTheory.SharedEEA.Alignment.Window

/-!
# Actual aligned physical frame and complete first-phase comparison

The actual first-phase shift rotates the old second work word while the
first word retains the entire original remainder and coefficient. Its
arithmetic window excludes the arbitrary low shift suffix
[LYL+26, sec_EEA/sub_regshare.tex:263-264,275-278]. The exact native signed
subtraction and low add-back preserve both whole words and put the full
strict shifted-divisor comparison in Sign.

This is a mathematical basis-frame description of the original registers.
No quotient is prepared or evaluated by a separate algorithm. The quotient
size only supplies a proved internal capacity bound; the native alignment
trajectory starts at shift zero and advances by its actual comparison.
The full Euclidean remainder can have a nonzero low suffix throughout.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AlignmentPhaseFrame

noncomputable section

open NumberTheory.SharedEEA ArithmeticWindowRegisters ArithmeticWindowLaws

private lemma shift_fits (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (within : shift ≤ state.quotient.size) : shift < 2 ^ modulus.size.size :=
  (within.trans (CoefficientPhaseFrame.quotient_size_le state modulus valid conserved)).trans_lt
    (Nat.lt_size_self modulus.size)

/-- Complete actual source frame at the retained alignment shift, before its flag update. -/
def frame (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (within : shift ≤ state.quotient.size) (sign iteration : Bool) : Registers modulus.size where
  firstWord := PackingBoundary.firstWord state modulus valid conserved
  secondWord := (WordRotation.packRotatedWork2 shift
    (DivisionCapacity.work2Payload state modulus valid conserved)).cast
      (DivisionCapacity.work2_width state modulus valid conserved)
  coefficientLength := BitVec.ofNatLT state.coefficient.size
    (CoefficientPhaseFrame.size_fits_counter
      (Capacity.iteration_fields_le state modulus valid conserved).2.2.1)
  quotientLength := 0
  divisorLength := BitVec.ofNatLT state.divisor.size
    (CoefficientPhaseFrame.size_fits_counter
      (Capacity.iteration_fields_le state modulus valid conserved).2.1)
  shift := BitVec.ofNatLT shift (shift_fits state modulus shift valid conserved within)
  flags := ⟨false, false, sign, iteration⟩
  control := false

/-- The actual stored lengths supply precisely the aligned source arithmetic geometry. -/
lemma window_fits (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) (sign iteration : Bool) :
    let physical := frame state modulus shift valid conserved within sign iteration
    physical.coefficientLength.toNat + physical.quotientLength.toNat + 1 + physical.shift.toNat ≤
      modulus.size + 3 :=
  AlignmentWindow.window_fits state modulus shift valid conserved active within

/-- The exact original physical region chosen by those actual stored lengths. -/
def window (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) : Window modulus.size :=
  remainderWindow modulus.size (state.coefficient.size + 1) shift
    (AlignmentWindow.window_fits state modulus shift valid conserved active within)

/-- The real rotated second-word slice contains the whole divisor even at the stopping threshold. -/
lemma sourceWord_toNat (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) (sign iteration : Bool) :
    (sourceWord (window state modulus shift valid conserved active within)
      (frame state modulus shift valid conserved within sign iteration)).toNat = state.divisor := by
  let selected := window state modulus shift valid conserved active within
  let physical := frame state modulus shift valid conserved within sign iteration
  have read := congrArg BitVec.toNat (wordEquiv_window selected physical.secondWord)
  change (sourceWord selected physical).toNat =
    (physical.secondWord.extractLsb' selected.below selected.length).toNat at read
  refine read.trans ?_
  change (((WordRotation.packRotatedWork2 shift
    (DivisionCapacity.work2Payload state modulus valid conserved)).cast
      (DivisionCapacity.work2_width state modulus valid conserved)).extractLsb'
        shift (AlignmentWindow.length state modulus shift)).toNat = _
  rw [BitVec.extractLsb'_cast]
  exact AlignmentWindow.source_toNat state modulus shift valid conserved active within

/-- The selected upper region plus its retained suffix is the entire original macro remainder. -/
lemma remainder_toNat (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) (sign iteration : Bool) :
    (RemainderReassembly.remainderWord (window state modulus shift valid conserved active within)
      (frame state modulus shift valid conserved within sign iteration)).toNat =
        state.remainder := by
  let selected := window state modulus shift valid conserved active within
  let payload := PackingBoundary.firstPayload state modulus valid conserved
  have fits := AlignmentWindow.window_fits state modulus shift valid conserved active within
  have region : selected.length + selected.below =
      PackingBoundary.firstRemainderWidth state modulus := by
    change modulus.size + 3 - (state.coefficient.size + 1) - shift + shift =
      modulus.size + 3 - (state.coefficient.size + 1)
    omega
  change (((WordPacking.packWork1 payload).cast
    (PackingBoundary.first_width state modulus valid conserved)).extractLsb' 0
      (selected.length + selected.below)).toNat = _
  rw [BitVec.extractLsb'_cast]
  exact (congrArg (fun length => ((WordPacking.packWork1 payload).extractLsb' 0 length).toNat)
    region).trans (congrArg BitVec.toNat (RemainderPhaseFrame.packWork1_read payload))

/-- The actual upper operand is the complete old remainder divided by its retained binary scale. -/
lemma targetWord_toNat (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) (sign iteration : Bool) :
    (targetWord (window state modulus shift valid conserved active within)
      (frame state modulus shift valid conserved within sign iteration)).toNat =
        state.remainder / 2 ^ shift := by
  have high := RemainderReassembly.target_toNat
    (window state modulus shift valid conserved active within)
    (frame state modulus shift valid conserved within sign iteration)
  exact high.trans (congrArg (fun value => value / 2 ^ shift)
    (remainder_toNat state modulus shift valid conserved active within sign iteration))

/-- The actual alignment arithmetic preserves both whole words and computes the strict full test. -/
lemma native_frame (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) (iteration : Bool) :
    ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus shift valid conserved within false iteration) =
      frame state modulus shift valid conserved within
        (decide (state.remainder < state.divisor * 2 ^ shift)) iteration := by
  let physical := frame state modulus shift valid conserved within false iteration
  have divisor : physical.divisorLength ≠ 0 := by
    intro zero
    have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
    change state.divisor.size = 0 at value
    have positive := Nat.size_pos.mpr active
    omega
  have actual := AlignmentBlockLaws.native_frame modulus.size physical rfl rfl rfl rfl divisor
    (window_fits state modulus shift valid conserved active within false iteration)
  change ArithmeticBlocks.remainderStep modulus.size physical =
    { physical with flags := { physical.flags with sign := (decide
      ((targetWord (window state modulus shift valid conserved active within)
        physical).toNat <
        (sourceWord (window state modulus shift valid conserved active within) physical).toNat)) } }
      at actual
  have comparison : decide (state.remainder / 2 ^ shift < state.divisor) =
      decide (state.remainder < state.divisor * 2 ^ shift) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using DivisionScale.underflow state.remainder state.divisor shift
  rw [targetWord_toNat state modulus shift valid conserved active within false iteration,
    sourceWord_toNat state modulus shift valid conserved active within false iteration,
    comparison] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.AlignmentPhaseFrame
