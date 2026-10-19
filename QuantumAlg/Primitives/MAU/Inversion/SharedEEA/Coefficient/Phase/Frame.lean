/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Replacement
import all QuantumAlg.Util.NumberTheory.SharedEEA.PackedCoefficient.Step

/-!
# Exact native coefficient-phase frame from the bounded Euclidean state

After the phase-three quotient swap, Work1 stores the fixed coefficient,
the remaining quotient after consumption, and the completed remainder;
Work2 keeps its old rotated coefficient/divisor payload. Sign contains the
consumed digit [LYL+26, sec_EEA/sub_regshare.tex:288-296]. This is a full
mathematical basis specification for the original physical registers, not
an input-dependent quantum preparation.

Every length and low counter is encoded without truncation using the
existing admissible-state and conserved-modulus bounds. The actual physical
window reads the already proved coefficient integer part and preserves
the possibly nonzero wrapped fraction
[LYL+26, sec_EEA/sub_regshare.tex:16-20,263-264]. The same existing native
coefficient program therefore produces the previously proved signed
coefficient instruction, with no extra window-value or addition-capacity
hypothesis. The preceding native selector reaching this frame and the full
phase trajectory are separate refinement obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientPhaseFrame

noncomputable section

open NumberTheory.SharedEEA

private lemma size_fits_counter {value modulus : Nat} (bounded : value ≤ modulus) :
    value.size < 2 ^ modulus.size.size :=
  (Nat.size_le_size bounded).trans_lt (Nat.lt_size_self modulus.size)

private lemma quotient_size_le (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.quotient.size ≤ modulus.size :=
  Nat.size_le_size ((Nat.div_le_self state.remainder state.divisor).trans
    (Capacity.iteration_fields_le state modulus valid conserved).1)

private lemma remaining_length_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.quotient.size - (count + 1) < 2 ^ modulus.size.size :=
  ((Nat.sub_le state.quotient.size (count + 1)).trans
    (quotient_size_le state modulus valid conserved)).trans_lt (Nat.lt_size_self modulus.size)

private lemma shift_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) :
    count < 2 ^ modulus.size.size :=
  (beforeEnd.trans_le (quotient_size_le state modulus valid conserved)).trans
    (Nat.lt_size_self modulus.size)

/-- Original physical frame immediately after consuming this phase-three quotient digit. -/
def frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    Registers modulus.size where
  firstWord := (WordPacking.packWork1
    (CoefficientCapacity.work1Payload state modulus (count + 1) valid conserved)).cast
      (CoefficientCapacity.work1_width state modulus (count + 1) valid conserved)
  secondWord := (PackedCoefficientWindow.word state modulus count valid conserved active).cast
    (CoefficientCapacity.work2_width state modulus valid conserved)
  coefficientLength := BitVec.ofNatLT state.coefficient.size
    (size_fits_counter (Capacity.iteration_fields_le state modulus valid conserved).2.2.1)
  quotientLength := BitVec.ofNatLT (state.quotient.size - (count + 1))
    (remaining_length_fits state modulus count valid conserved)
  divisorLength := BitVec.ofNatLT state.divisor.size
    (size_fits_counter (Capacity.iteration_fields_le state modulus valid conserved).2.1)
  shift := BitVec.ofNatLT count (shift_fits state modulus count valid conserved beforeEnd)
  flags := ⟨true, false, CoefficientPhase.lowBit (CoefficientWindow.current state count).remaining,
    iteration⟩
  control := false

/-- The real coefficient length is the actual coefficient bit length, without modular truncation. -/
lemma frame_coefficientLength (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (frame state modulus count valid conserved active beforeEnd iteration).coefficientLength.toNat =
      state.coefficient.size := rfl

/-- The native remaining-quotient field is the actual bit length after this consumed digit. -/
lemma frame_quotientLength (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (frame state modulus count valid conserved active beforeEnd iteration).quotientLength.toNat =
      (CoefficientWindow.current state (count + 1)).remaining.size := by
  rw [CoefficientCapacity.remaining_size]
  rfl

/-- The retained low shift is the actual circular-rotation count, not a guessed quotient scale. -/
lemma frame_shift (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (frame state modulus count valid conserved active beforeEnd iteration).shift.toNat = count :=
  rfl

/-- Existing reachable coefficient bounds supply the physical arithmetic window internally. -/
lemma window_fits (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    CoefficientWindow.width state ≤ modulus.size + 3 := by
  have bounded := Nat.size_le_size
    (Capacity.iteration_fields_le state modulus valid conserved).2.2.1
  unfold CoefficientWindow.width
  omega

/-- The actual original coefficient window contains the coefficient bits and its separator. -/
def window (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    ArithmeticWindowRegisters.Window modulus.size :=
  CoefficientWindowOrientation.coefficientWindow modulus.size (CoefficientWindow.width state)
    (window_fits state modulus valid conserved)

private lemma read_cast {left right length : Nat} (word : BitVec left) (same : left = right) :
    PhysicalWindow.read length (word.cast same) = PhysicalWindow.read length word := by
  cases same
  rfl

private lemma packWork1_read {coefficient quotient remainder : Nat}
    (payload : WordPacking.Work1Payload coefficient quotient remainder) :
    PhysicalWindow.read (coefficient + 1) (WordPacking.packWork1 payload) =
      payload.coefficientBits.setWidth (coefficient + 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  rw [PhysicalWindow.read_bit (WordPacking.packWork1 payload)
    (by omega : coefficient + 1 ≤ (coefficient + 1) + (quotient + remainder)) index within,
    BitVec.getLsbD_setWidth]
  simp only [within, decide_true, Bool.true_and]
  by_cases inside : index < coefficient
  · exact WordPacking.packWork1_coefficient_bit payload index inside
  · have atSeparator : index = coefficient := by omega
    subst index
    rw [WordPacking.packWork1_separator]
    exact (BitVec.getLsbD_of_ge payload.coefficientBits coefficient (Nat.le_refl _)).symm

/-- The actual physical Work1 read is precisely the existing bounded coefficient operand. -/
lemma sourceWord_eq (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    CoefficientWindowLaws.sourceWord (window state modulus valid conserved)
      (frame state modulus count valid conserved active beforeEnd iteration) =
        CoefficientWindow.coefficientWord state := by
  change PhysicalWindow.read (state.coefficient.size + 1)
    ((WordPacking.packWork1
      (CoefficientCapacity.work1Payload state modulus (count + 1) valid conserved)).cast
        (CoefficientCapacity.work1_width state modulus (count + 1) valid conserved)) = _
  rw [read_cast, packWork1_read]
  apply BitVec.eq_of_toNat_eq
  exact BitVec.toNat_setWidth_of_le
    (by omega : state.coefficient.size ≤ state.coefficient.size + 1)

/-- The actual rotated Work2 read is the proved integer part, with no divisibility premise. -/
lemma targetWord_eq (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    CoefficientWindowLaws.targetWord (window state modulus valid conserved)
      (frame state modulus count valid conserved active beforeEnd iteration) =
        CoefficientWindow.valueWord state count valid := by
  change PhysicalWindow.read (CoefficientWindow.width state)
    ((PackedCoefficientWindow.word state modulus count valid conserved active).cast
      (CoefficientCapacity.work2_width state modulus valid conserved)) = _
  rw [read_cast]
  exact PackedCoefficientWindow.read_eq state modulus count valid conserved active beforeEnd.le

/-- The existing actual native program computes the proved coefficient instruction on this frame. -/
lemma native_signed_word (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    CoefficientWindowLaws.signedTarget (window state modulus valid conserved)
      (ArithmeticBlocks.coefficientStep modulus.size
        (frame state modulus count valid conserved active beforeEnd iteration)) =
      (CoefficientWindow.instruction state count valid).2 := by
  have actual := CoefficientBlockLaws.native_signed_word modulus.size
    (frame state modulus count valid conserved active beforeEnd iteration) rfl rfl rfl
    (window_fits state modulus valid conserved)
  change CoefficientWindowLaws.signedTarget (window state modulus valid conserved)
      (ArithmeticBlocks.coefficientStep modulus.size
        (frame state modulus count valid conserved active beforeEnd iteration)) =
    SignedCoefficient.addBit
      (CoefficientWindowLaws.targetWord (window state modulus valid conserved)
        (frame state modulus count valid conserved active beforeEnd iteration))
      (CoefficientWindowLaws.sourceWord (window state modulus valid conserved)
        (frame state modulus count valid conserved active beforeEnd iteration))
      (CoefficientPhase.lowBit (CoefficientWindow.current state count).remaining) at actual
  rw [targetWord_eq, sourceWord_eq] at actual
  exact actual

/-- Reachable capacity clears the actual native Sign; no external addition-range premise is used. -/
lemma native_sign_clear (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (ArithmeticBlocks.coefficientStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).flags.sign =
        false := by
  let output := ArithmeticBlocks.coefficientStep modulus.size
    (frame state modulus count valid conserved active beforeEnd iteration)
  have actual : (CoefficientWindowLaws.signedTarget (window state modulus valid conserved)
      output).msb = (CoefficientWindow.instruction state count valid).2.msb :=
    congrArg (fun word : BitVec (CoefficientWindow.width state + 1) => word.msb)
      (native_signed_word state modulus count valid conserved active beforeEnd iteration)
  have head : (CoefficientWindowLaws.signedTarget (window state modulus valid conserved)
      output).msb = output.flags.sign := BitVec.msb_cons
  exact head.symm.trans (actual.trans (CoefficientWindow.instruction_clears state count valid).2)

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientPhaseFrame
