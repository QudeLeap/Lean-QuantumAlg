/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Reassembly
import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Window

/-!
# Actual shared-register basis frames at phase-two arithmetic entry

The source first right-rotates Work2 and decrements shift, then subtracts
at the current physical remainder window
[LYL+26, sec_EEA/sub_regshare.tex:279-287]. These basis frames contain the
existing packed Work1 state and the complete Work2 payload at that actual
rotation. The logical division position supplies the finite lengths and
all original five control bits, retaining arbitrary Iter.

This is a physical basis specification for trajectory refinement, not an
input-dependent quantum preparation. Every finite-field and operand bound
is derived from the reachable macro invariant and actual alignment count.
The window reads the real divisor and the high part of the complete old
remainder; the remaining low bits are still present in Work1. No zero-low
or shorter-old-remainder premise is imposed.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.RemainderPhaseFrame

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowLaws RemainderReassembly
open NumberTheory.SharedEEA

private theorem size_fits_counter {value modulus : Nat} (bounded : value ≤ modulus) :
    value.size < 2 ^ modulus.size.size :=
  (Nat.size_le_size bounded).trans_lt (Nat.lt_size_self modulus.size)

private theorem alignment_le (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    (Alignment.align state.remainder state.divisor).places ≤ modulus.size :=
  (Alignment.align_places_le state.remainder state.divisor).trans
    (Nat.size_le_size (Capacity.iteration_fields_le state modulus valid conserved).1)

private theorem count_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    count < 2 ^ modulus.size.size :=
  (beforeEnd.trans_le (alignment_le state modulus valid conserved)).trans
    (Nat.lt_size_self modulus.size)

private theorem shift_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    DivisionWindow.shift state count < 2 ^ modulus.size.size :=
  ((Nat.sub_le (Alignment.align state.remainder state.divisor).places (count + 1)).trans
    (alignment_le state modulus valid conserved)).trans_lt
    (Nat.lt_size_self modulus.size)

/-- The complete physical frame after the actual phase-two pre-shift and before subtraction. -/
def frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) : Registers modulus.size where
  firstWord := (WordPacking.packWork1
    (DivisionCapacity.work1Payload state modulus count valid conserved active beforeEnd.le)).cast
      (DivisionCapacity.work1_width state modulus count valid conserved active beforeEnd.le)
  secondWord := (WordRotation.packRotatedWork2 (DivisionWindow.shift state count)
    (DivisionCapacity.work2Payload state modulus valid conserved)).cast
      (DivisionCapacity.work2_width state modulus valid conserved)
  coefficientLength := BitVec.ofNatLT state.coefficient.size
    (size_fits_counter (Capacity.iteration_fields_le state modulus valid conserved).2.2.1)
  quotientLength := BitVec.ofNatLT count (count_fits state modulus count valid conserved beforeEnd)
  divisorLength := BitVec.ofNatLT state.divisor.size
    (size_fits_counter (Capacity.iteration_fields_le state modulus valid conserved).2.1)
  shift := BitVec.ofNatLT (DivisionWindow.shift state count)
    (shift_fits state modulus count valid conserved)
  flags := ⟨false, true, false, iteration⟩
  control := false

/-- Actual stored quotient length equals the already written pure division prefix length. -/
theorem frame_quotientLength (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (frame state modulus count valid conserved active beforeEnd iteration).quotientLength.toNat =
      (DivisionProgress.current state count).written := by
  rw [DivisionProgress.current_written]
  rfl

/-- Reachable threshold capacity supplies the actual native window bound internally. -/
theorem window_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    state.coefficient.size + count + 1 + DivisionWindow.shift state count ≤ modulus.size + 3 := by
  have fits := DivisionWindow.window_fits state modulus count valid conserved active beforeEnd
  unfold DivisionWindow.above at fits
  omega

/-- The exact physical region selected by these actual stored finite lengths. -/
def window (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    Window modulus.size :=
  remainderWindow modulus.size (state.coefficient.size + count + 1)
    (DivisionWindow.shift state count)
    (window_fits state modulus count valid conserved active beforeEnd)

private theorem window_length (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (window state modulus count valid conserved active beforeEnd).length =
      DivisionWindow.length state modulus count := by
  have ordered : state.coefficient.size + count + 1 = state.coefficient.size + 1 + count := by
    omega
  exact congrArg (fun start => modulus.size + 3 - start - DivisionWindow.shift state count) ordered

/-- The upper window plus its retained low suffix is exactly the full old remainder width. -/
theorem remainder_width (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (window state modulus count valid conserved active beforeEnd).length +
        (window state modulus count valid conserved active beforeEnd).below =
      DivisionCapacity.remainderWidth state modulus count := by
  have fits := window_fits state modulus count valid conserved active beforeEnd
  change (modulus.size + 3 - (state.coefficient.size + count + 1) -
    DivisionWindow.shift state count) + DivisionWindow.shift state count = _
  unfold DivisionCapacity.remainderWidth
  rw [DivisionProgress.current_written]
  omega

/-- The actual shifted Work2 window contains precisely the complete untruncated divisor. -/
theorem sourceWord_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (sourceWord (window state modulus count valid conserved active beforeEnd)
      (frame state modulus count valid conserved active beforeEnd iteration)).toNat =
        state.divisor := by
  let selected := window state modulus count valid conserved active beforeEnd
  let physical := frame state modulus count valid conserved active beforeEnd iteration
  have read := congrArg BitVec.toNat (wordEquiv_window selected physical.secondWord)
  change (sourceWord selected physical).toNat =
    (physical.secondWord.extractLsb' selected.below selected.length).toNat at read
  refine read.trans ?_
  change (((WordRotation.packRotatedWork2 (DivisionWindow.shift state count)
    (DivisionCapacity.work2Payload state modulus valid conserved)).cast
      (DivisionCapacity.work2_width state modulus valid conserved)).extractLsb'
        (DivisionWindow.shift state count) selected.length).toNat = _
  rw [BitVec.extractLsb'_cast]
  exact (congrArg (fun length => ((WordRotation.packRotatedWork2 (DivisionWindow.shift state count)
      (DivisionCapacity.work2Payload state modulus valid conserved)).extractLsb'
        (DivisionWindow.shift state count) length).toNat)
    (window_length state modulus count valid conserved active beforeEnd)).trans
      (DivisionWindow.source_toNat state modulus count valid conserved active beforeEnd)

private theorem packWork1_read {coefficientWidth quotientWidth remainderWidth : Nat}
    (payload : WordPacking.Work1Payload coefficientWidth quotientWidth remainderWidth) :
    (WordPacking.packWork1 payload).extractLsb' 0 remainderWidth = payload.remainderBits := by
  have read := congrArg
    (fun value : WordPacking.Work1Payload coefficientWidth quotientWidth remainderWidth =>
      value.remainderBits) (WordPacking.unpackWork1_packWork1 payload)
  change ((WordPacking.packWork1 payload).extractLsb'
    0 (quotientWidth + remainderWidth)).extractLsb' 0 remainderWidth = payload.remainderBits at read
  have flatten : ((WordPacking.packWork1 payload).extractLsb'
      0 (quotientWidth + remainderWidth)).extractLsb' 0 remainderWidth =
        (WordPacking.packWork1 payload).extractLsb' 0 remainderWidth :=
    BitVec.extractLsb'_extractLsb'_of_le (by omega)
  exact flatten.symm.trans read

/-- The complete old physical remainder, including all low shift bits, is the actual pure state. -/
theorem remainder_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (remainderWord (window state modulus count valid conserved active beforeEnd)
      (frame state modulus count valid conserved active beforeEnd iteration)).toNat =
        (DivisionProgress.current state count).remainder := by
  let selected := window state modulus count valid conserved active beforeEnd
  let payload := DivisionCapacity.work1Payload state modulus count
    valid conserved active beforeEnd.le
  change (((WordPacking.packWork1 payload).cast
    (DivisionCapacity.work1_width state modulus count
      valid conserved active beforeEnd.le)).extractLsb' 0
        (selected.length + selected.below)).toNat = _
  rw [BitVec.extractLsb'_cast]
  exact (congrArg (fun length => ((WordPacking.packWork1 payload).extractLsb' 0 length).toNat)
    (remainder_width state modulus count valid conserved active beforeEnd)).trans
      (congrArg BitVec.toNat (packWork1_read payload))

/-- The actual high target equals the old remainder divided by the real remaining binary scale. -/
theorem targetWord_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (targetWord (window state modulus count valid conserved active beforeEnd)
      (frame state modulus count valid conserved active beforeEnd iteration)).toNat =
        (DivisionProgress.current state count).remainder /
          2 ^ DivisionWindow.shift state count := by
  have high := RemainderReassembly.target_toNat
    (window state modulus count valid conserved active beforeEnd)
    (frame state modulus count valid conserved active beforeEnd iteration)
  exact high.trans (congrArg (fun value => value / 2 ^ DivisionWindow.shift state count)
    (remainder_toNat state modulus count valid conserved active beforeEnd iteration))

end

end QuantumAlg.MAU.Inversion.SharedEEA.RemainderPhaseFrame
