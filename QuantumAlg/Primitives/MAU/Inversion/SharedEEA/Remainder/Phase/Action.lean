/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Phase.Frame
import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Division.Phase

/-!
# Actual native remainder arithmetic at every reachable division position

The actual signed subtraction, Sign complement, and add-back now act on
the exact packed phase-entry frame
[LYL+26, sec_EEA/sub_regshare.tex:279-287;
LYL+26, sec_EEA/sub_opt.tex:43-48]. Reading their complete physical
remainder region gives precisely the next `DivisionProgress.current`
remainder. The actual Sign is the same weak-comparison quotient digit.

Every field width and arithmetic scale is derived from the reachable
macro invariant. In particular the next-state capacity is proved for
the actual native output, after full subtraction has occurred. This
prepares the real Sign/quotient exchange without assuming that the old
remainder fits the shorter field. The outside tuple retains all original
prefix, suffix, length, phase, Iter, and Ctrl coordinates jointly.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.RemainderPhaseAction

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowLaws RemainderReassembly RemainderPhaseFrame
open NumberTheory.SharedEEA

private lemma frame_divisor_nonzero (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (frame state modulus count valid conserved active beforeEnd iteration).divisorLength ≠ 0 := by
  intro zero
  have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
  change state.divisor.size = 0 at value
  have positive := Nat.size_pos.mpr active
  omega

private lemma scaled_threshold (state : IterationState) (count : Nat)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    state.divisor * 2 ^ DivisionWindow.shift state count =
      DivisionThreshold.threshold state count :=
  (Nat.mul_comm _ _).trans (DivisionThreshold.threshold_eq state count active beforeEnd).symm

/-- The existing native block computes the exact next full remainder on every reachable frame. -/
lemma native_remainder (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (remainderWord (window state modulus count valid conserved active beforeEnd)
      (ArithmeticBlocks.remainderStep modulus.size
        (frame state modulus count valid conserved active beforeEnd iteration))).toNat =
      (DivisionProgress.current state (count + 1)).remainder := by
  let selected := window state modulus count valid conserved active beforeEnd
  let original := frame state modulus count valid conserved active beforeEnd iteration
  have actual := RemainderReassembly.native_remainder_toNat modulus.size original rfl rfl rfl rfl
    (frame_divisor_nonzero state modulus count valid conserved active beforeEnd iteration)
    (window_fits state modulus count valid conserved active beforeEnd)
  change (remainderWord selected (ArithmeticBlocks.remainderStep modulus.size original)).toNat =
    (if (sourceWord selected original).toNat * 2 ^ DivisionWindow.shift state count ≤
        (remainderWord selected original).toNat
      then (remainderWord selected original).toNat -
        (sourceWord selected original).toNat * 2 ^ DivisionWindow.shift state count
      else (remainderWord selected original).toNat) at actual
  have source := sourceWord_toNat state modulus count valid conserved active beforeEnd iteration
  have remainder := RemainderPhaseFrame.remainder_toNat state modulus count
    valid conserved active beforeEnd iteration
  change (sourceWord selected original).toNat = state.divisor at source
  change (remainderWord selected original).toNat =
    (DivisionProgress.current state count).remainder at remainder
  rw [source, remainder, scaled_threshold state count active beforeEnd] at actual
  exact actual.trans (SignedDivisionPhase.next_remainder state count).symm

/-- The actual Sign is precisely the quotient bit required by the next pure division state. -/
lemma native_digit (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).flags.sign =
        decide (DivisionThreshold.threshold state count ≤
          (DivisionProgress.current state count).remainder) := by
  let selected := window state modulus count valid conserved active beforeEnd
  let original := frame state modulus count valid conserved active beforeEnd iteration
  have actual := RemainderReassembly.source_sign original rfl rfl rfl
    (frame_divisor_nonzero state modulus count valid conserved active beforeEnd iteration)
    (window_fits state modulus count valid conserved active beforeEnd)
  change (ArithmeticBlocks.remainderSource original).flags.sign =
    decide ((sourceWord selected original).toNat * 2 ^ DivisionWindow.shift state count ≤
      (remainderWord selected original).toNat) at actual
  have source := sourceWord_toNat state modulus count valid conserved active beforeEnd iteration
  have remainder := RemainderPhaseFrame.remainder_toNat state modulus count
    valid conserved active beforeEnd iteration
  change (sourceWord selected original).toNat = state.divisor at source
  change (remainderWord selected original).toNat =
    (DivisionProgress.current state count).remainder at remainder
  rw [source, remainder, scaled_threshold state count active beforeEnd] at actual
  exact (congrArg (fun value : Registers modulus.size => value.flags.sign)
    (ArithmeticBlocks.remainderStep_eq_source modulus.size original rfl)).trans actual

/-- Reachable next capacity bounds the actual output after subtraction, without narrowing input. -/
lemma native_next_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (remainderWord (window state modulus count valid conserved active beforeEnd)
      (ArithmeticBlocks.remainderStep modulus.size
        (frame state modulus count valid conserved active beforeEnd iteration))).toNat <
      2 ^ SignedDivisionPhase.nextWidth state modulus count := by
  rw [native_remainder]
  exact DivisionCapacity.remainder_fits state modulus (count + 1)
    valid conserved active (by omega)

/-- The actual complementary coordinates remain jointly unchanged at every reachable position. -/
lemma native_complement (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (grouping (window state modulus count valid conserved active beforeEnd)
      (ArithmeticBlocks.remainderStep modulus.size
        (frame state modulus count valid conserved active beforeEnd iteration))).2 =
      (grouping (window state modulus count valid conserved active beforeEnd)
        (frame state modulus count valid conserved active beforeEnd iteration)).2 := by
  rw [ArithmeticBlocks.remainderStep_eq_source modulus.size _ rfl]
  exact RemainderBlockLaws.source_complement
    (frame state modulus count valid conserved active beforeEnd iteration) rfl rfl
    (window_fits state modulus count valid conserved active beforeEnd)

end

end QuantumAlg.MAU.Inversion.SharedEEA.RemainderPhaseAction
