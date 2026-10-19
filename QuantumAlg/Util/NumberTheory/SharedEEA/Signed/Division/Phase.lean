/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Threshold
import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Division

/-!
# Concrete signed instructions at the actual division-phase widths

This owner connects the source's literal signed subtraction, conditional
add-back, sign complement, and quotient-bit swap to the already proved
division microstate [LYL+26, sec_EEA/sub_regshare.tex:279-287]. Both operands
use the actual old remainder region. Its width is proved to be exactly one
more than the next remainder region, so the old high bit survives until
the swap. The actual next-state capacity establishes that the swap clears
`Sign`; no extra caller input condition is introduced.

The resulting physical quotient bit gives precisely the next effective
quotient prefix, and the low output bits give precisely the next actual
remainder. Reading that written bit reverses the concrete word instruction.
These are the signed arithmetic instructions on the selected region, not
a quantum implementation or a separate division execution engine.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.SignedDivisionPhase

/-- The actual region left for the remainder after writing the next quotient bit. -/
def nextWidth (state : IterationState) (modulus count : Nat) : Nat :=
  DivisionCapacity.remainderWidth state modulus (count + 1)

/-- Encode the actual old remainder at its full pre-subtraction width. -/
def valueWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    BitVec (nextWidth state modulus count + 1) :=
  BitVec.ofNatLT (DivisionProgress.current state count).remainder (by
    have fits := DivisionCapacity.remainder_fits state modulus count
      valid conserved active beforeEnd.le
    rw [DivisionThreshold.remainder_width_succ state modulus count
      valid conserved active beforeEnd] at fits
    exact fits)

/-- The word given to subtraction is exactly the already encoded source remainder region. -/
lemma valueWord_eq_payload (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    valueWord state modulus count valid conserved active beforeEnd =
      (DivisionCapacity.work1Payload state modulus count
        valid conserved active beforeEnd.le).remainderBits.cast
          (DivisionThreshold.remainder_width_succ state modulus count
            valid conserved active beforeEnd) := by
  apply BitVec.eq_of_toNat_eq
  change (DivisionProgress.current state count).remainder =
    ((DivisionCapacity.work1Payload state modulus count
      valid conserved active beforeEnd.le).remainderBits.cast
        (DivisionThreshold.remainder_width_succ state modulus count
          valid conserved active beforeEnd)).toNat
  exact (BitVec.toNat_cast
    (DivisionThreshold.remainder_width_succ state modulus count valid conserved active beforeEnd)
    (DivisionCapacity.work1Payload state modulus count
      valid conserved active beforeEnd.le).remainderBits).symm

/-- Encode the actual shifted threshold in the same old region, using the derived source bound. -/
def thresholdWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    BitVec (nextWidth state modulus count + 1) :=
  BitVec.ofNatLT (DivisionThreshold.threshold state count) (by
    have fits := DivisionThreshold.threshold_fits_next state modulus count
      valid conserved active beforeEnd
    exact fits.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by
      change nextWidth state modulus count ≤ nextWidth state modulus count + 1
      omega)))

/-- The old-width operand retains every bit of the actual intermediate remainder. -/
lemma valueWord_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (valueWord state modulus count valid conserved active beforeEnd).toNat =
      (DivisionProgress.current state count).remainder := by
  rfl

/-- The threshold operand retains exactly the actual right-shifted divisor value. -/
lemma thresholdWord_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (thresholdWord state modulus count valid conserved active beforeEnd).toNat =
      DivisionThreshold.threshold state count := by
  rfl

/-- The actual next division state uses exactly the comparison implemented by the signed words. -/
lemma next_remainder (state : IterationState) (count : Nat) :
    (DivisionProgress.current state (count + 1)).remainder =
      if DivisionThreshold.threshold state count ≤ (DivisionProgress.current state count).remainder
      then (DivisionProgress.current state count).remainder -
        DivisionThreshold.threshold state count
      else (DivisionProgress.current state count).remainder := by
  rw [DivisionThreshold.current_step]
  rfl

/-- The next-state invariant supplies the signed instruction's shrinking condition. -/
lemma next_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (if (thresholdWord state modulus count valid conserved active beforeEnd).toNat ≤
        (valueWord state modulus count valid conserved active beforeEnd).toNat
      then (valueWord state modulus count valid conserved active beforeEnd).toNat -
        (thresholdWord state modulus count valid conserved active beforeEnd).toNat
      else (valueWord state modulus count valid conserved active beforeEnd).toNat) <
        2 ^ nextWidth state modulus count := by
  rw [valueWord_toNat, thresholdWord_toNat, ← next_remainder]
  exact DivisionCapacity.remainder_fits state modulus (count + 1)
    valid conserved active (by omega)

/-- Apply the concrete source instructions to the exact region selected by the actual microstate. -/
def instruction (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    Bool × BitVec (nextWidth state modulus count + 1) :=
  SignedDivision.extract (valueWord state modulus count valid conserved active beforeEnd)
    (thresholdWord state modulus count valid conserved active beforeEnd)

/-- Actual signed instructions clear Sign and compute the exact next quotient bit and remainder. -/
lemma instruction_spec (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (instruction state modulus count valid conserved active beforeEnd).1 = false ∧
      (instruction state modulus count valid conserved active beforeEnd).2.msb =
        decide (DivisionThreshold.threshold state count ≤
          (DivisionProgress.current state count).remainder) ∧
      ((instruction state modulus count valid conserved active beforeEnd).2.setWidth
        (nextWidth state modulus count)).toNat =
          (DivisionProgress.current state (count + 1)).remainder := by
  obtain ⟨sign, digit, remainder⟩ := SignedDivision.extract_spec
    (valueWord state modulus count valid conserved active beforeEnd)
    (thresholdWord state modulus count valid conserved active beforeEnd)
    (next_fits state modulus count valid conserved active beforeEnd)
  refine ⟨sign, ?_, ?_⟩
  · unfold instruction
    simpa only [valueWord_toNat, thresholdWord_toNat] using digit
  · unfold instruction
    simpa only [valueWord_toNat, thresholdWord_toNat, ← next_remainder] using remainder

/-- Appending the actual output bit produces precisely the next source quotient prefix. -/
lemma instruction_quotient (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (DivisionProgress.current state (count + 1)).quotientPrefix =
      2 * (DivisionProgress.current state count).quotientPrefix +
        if (instruction state modulus count valid conserved active beforeEnd).2.msb
          then 1 else 0 := by
  rw [(instruction_spec state modulus count valid conserved active beforeEnd).2.1,
    DivisionThreshold.current_step]
  change 2 * (DivisionProgress.current state count).quotientPrefix +
      (if DivisionThreshold.threshold state count ≤ (DivisionProgress.current state count).remainder
        then 1 else 0) =
    2 * (DivisionProgress.current state count).quotientPrefix +
      if decide (DivisionThreshold.threshold state count ≤
        (DivisionProgress.current state count).remainder) then 1 else 0
  by_cases selected : DivisionThreshold.threshold state count ≤
      (DivisionProgress.current state count).remainder <;> simp [selected]

/-- The actual output bit reconstructs the old source region without an extra domain hypothesis. -/
lemma instruction_rewind (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    SignedDivision.rewind (thresholdWord state modulus count valid conserved active beforeEnd)
        (instruction state modulus count valid conserved active beforeEnd) =
      valueWord state modulus count valid conserved active beforeEnd :=
  SignedDivision.rewind_extract _ _ (next_fits state modulus count valid conserved active beforeEnd)

/-- The actual prime-input path reaches the shrinking-field boundary and computes it correctly. -/
lemma prime_twenty_nine_actual_step :
    let state := IterationState.initial 29 (foldInput 29 3).2
    let valid := folded_initial_admissible 29 3 (by decide) (by decide)
    let conserved := IterationState.initial_balance 29 (foldInput 29 3).2
    let active : 0 < state.divisor := by decide
    let beforeEnd : 3 < (Alignment.align state.remainder state.divisor).places := by decide
    (valueWord state 29 3 valid conserved active beforeEnd).toNat = 5 ∧
      (thresholdWord state 29 3 valid conserved active beforeEnd).toNat = 3 ∧
      (instruction state 29 3 valid conserved active beforeEnd).1 = false ∧
      (instruction state 29 3 valid conserved active beforeEnd).2.toNat = 6 ∧
      (DivisionProgress.current state 4).remainder = 2 := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.SignedDivisionPhase
