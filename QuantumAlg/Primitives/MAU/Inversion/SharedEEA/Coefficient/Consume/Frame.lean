/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Phase.Frame
import all QuantumAlg.Util.NumberTheory.SharedEEA.Coefficient.PackedStep

/-!
# Reachable physical frame before actual phase-three quotient consumption

The complete basis frame has the live quotient suffix, zero Sign, the
current rotated Work2, and the existing finite lengths immediately before
the source Sign/quotient exchange
[LYL+26, sec_EEA/sub_regshare.tex:288-296]. Actual macro capacity establishes
that the last quotient coordinate is physically present. Reading it gives
the real lowest remaining quotient bit; reading above and below it gives
the exact retained prefix and full old remainder.

This is a basis specification used to prove the existing native program,
not a quantum preparation with input-dependent fields. Every position,
finite decrement, and width relation follows from the original admissible
macro invariant; none becomes a new caller-supplied fit condition.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientConsumeFrame

noncomputable section

open NumberTheory.SharedEEA

private theorem remaining_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.quotient.size - count < 2 ^ modulus.size.size :=
  ((Nat.sub_le state.quotient.size count).trans
    (CoefficientPhaseFrame.quotient_size_le state modulus valid conserved)).trans_lt
      (Nat.lt_size_self modulus.size)

/-- Complete original frame immediately before the actual phase-three Sign/quotient program. -/
def frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    Registers modulus.size :=
  { CoefficientPhaseFrame.frame state modulus count valid conserved active beforeEnd iteration with
    firstWord := (WordPacking.packWork1
      (CoefficientCapacity.work1Payload state modulus count valid conserved)).cast
        (CoefficientCapacity.work1_width state modulus count valid conserved)
    quotientLength := BitVec.ofNatLT (state.quotient.size - count)
      (remaining_fits state modulus count valid conserved)
    flags := ⟨true, false, false, iteration⟩ }

/-- The actual last retained quotient position fits without a new physical-range premise. -/
def position (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) : Fin (modulus.size + 3) :=
  ⟨state.coefficient.size + (state.quotient.size - count), by
    have capacity := CoefficientCapacity.work1_capacity state modulus count valid conserved
    omega⟩

/-- This is exactly the natural sum read by the live native selector, without finite truncation. -/
theorem position_val (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    let physical := frame state modulus count valid conserved active beforeEnd iteration
    (position state modulus count valid conserved).val =
      physical.coefficientLength.toNat + physical.quotientLength.toNat := rfl

/-- The physical lower region is the whole old remainder before its leading bit expands. -/
theorem position_lowWidth (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    modulus.size + 3 - 1 - (position state modulus count valid conserved).val =
      CoefficientCapacity.work1RemainderWidth state modulus count := by
  change modulus.size + 3 - 1 - (state.coefficient.size + (state.quotient.size - count)) =
    modulus.size + 3 - (state.coefficient.size + 1 + (state.quotient.size - count))
  omega

/-- The retained prefix consists of the coefficient, separator, and next shorter quotient suffix. -/
theorem position_prefixWidth (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) :
    (position state modulus count valid conserved).val =
      (state.coefficient.size + 1) + (state.quotient.size - (count + 1)) := by
  change state.coefficient.size + (state.quotient.size - count) = _
  omega

/-- The actual complete prefix is exactly the next logical quotient prefix at its actual width. -/
theorem firstWord_prefix (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    ((frame state modulus count valid conserved active beforeEnd iteration).firstWord.extractLsb'
      (modulus.size + 3 - 1 - (position state modulus count valid conserved).val + 1)
      (position state modulus count valid conserved).val).toNat =
        (CoefficientPackedStep.retainedPrefix state modulus count valid conserved).toNat := by
  rw [position_lowWidth, position_prefixWidth state modulus count valid conserved beforeEnd]
  change (((WordPacking.packWork1
    (CoefficientCapacity.work1Payload state modulus count valid conserved)).cast
      (CoefficientCapacity.work1_width state modulus count
        valid conserved)).extractLsb' _ _).toNat = _
  rw [BitVec.extractLsb'_cast]
  exact CoefficientPackedStep.original_prefix state modulus count valid conserved beforeEnd

/-- Reading below the real consumed quotient bit retains every original remainder bit. -/
theorem firstWord_low (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    ((frame state modulus count valid conserved active beforeEnd iteration).firstWord.setWidth
      (modulus.size + 3 - 1 - (position state modulus count valid conserved).val)).toNat =
        state.remainder % state.divisor := by
  rw [position_lowWidth]
  change (((WordPacking.packWork1
    (CoefficientCapacity.work1Payload state modulus count valid conserved)).cast
      (CoefficientCapacity.work1_width state modulus count valid conserved)).setWidth _).toNat = _
  rw [BitVec.setWidth_cast, CoefficientPackedStep.original_low]
  rfl

/-- The actual selected wire is the next low quotient digit consumed by coefficient arithmetic. -/
theorem firstWord_digit (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (frame state modulus count valid conserved active beforeEnd iteration).firstWord.getMsbD
      (position state modulus count valid conserved).val =
        CoefficientPhase.lowBit (CoefficientWindow.current state count).remaining := by
  rw [BitVec.getMsbD_eq_getLsbD,
    decide_eq_true (position state modulus count valid conserved).isLt, Bool.true_and,
    position_lowWidth]
  change ((WordPacking.packWork1
    (CoefficientCapacity.work1Payload state modulus count valid conserved)).cast
      (CoefficientCapacity.work1_width state modulus count valid conserved)).getLsbD _ = _
  rw [BitVec.getLsbD_cast]
  exact CoefficientPackedStep.original_digit state modulus count valid conserved beforeEnd

/-- Actual finite decrement equals the next live quotient length, with internal no-wrap evidence. -/
theorem quotientLength_subtract (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (frame state modulus count valid conserved active beforeEnd iteration).quotientLength - 1 =
      (CoefficientPhaseFrame.frame state modulus count
        valid conserved active beforeEnd iteration).quotientLength := by
  have remaining := remaining_fits state modulus count valid conserved
  have oneFits : 1 < 2 ^ modulus.size.size := by omega
  have countEq : state.quotient.size - (count + 1) + 1 = state.quotient.size - count := by omega
  rw [BitVec.sub_eq_iff_eq_add]
  apply BitVec.eq_of_toNat_eq
  change state.quotient.size - count =
    ((CoefficientPhaseFrame.frame state modulus count
      valid conserved active beforeEnd iteration).quotientLength + 1).toNat
  rw [BitVec.toNat_add]
  change state.quotient.size - count =
    (state.quotient.size - (count + 1) + 1 % 2 ^ modulus.size.size) % 2 ^ modulus.size.size
  rw [Nat.mod_eq_of_lt oneFits, countEq, Nat.mod_eq_of_lt remaining]

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientConsumeFrame
