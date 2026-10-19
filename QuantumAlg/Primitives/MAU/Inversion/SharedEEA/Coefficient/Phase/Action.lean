/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Phase.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Shift

/-!
# Actual coefficient arithmetic and post-shift reach the next packed Work2

The existing native coefficient program writes the exact next integer
window into the complete old rotated payload. Its actual guarded post-shift
then rotates that complete word once, as prescribed by the phase-three
source [LYL+26, sec_EEA/sub_regshare.tex:288-296;
LYL+26, sec_EEA/sub_opt.tex:61-70]. The result is the previously proved
next packed coefficient state, including the original divisor and every
possibly nonzero fractional bit.

The physical field bounds and arithmetic window values are obtained from
`CoefficientPhaseFrame`, not supplied by a caller. These statements concern
the actual program components of `NativeMicrostep`. Reaching the frame
through its preceding selector and the later phase/boundary dispatch are
separate remaining full-trajectory obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientPhaseAction

noncomputable section

open NumberTheory.SharedEEA CoefficientPhaseFrame

private lemma replace_cast {left right length : Nat} (word : BitVec left)
    (replacement : BitVec length) (same : left = right)
    (leftFit : length ≤ left) (rightFit : length ≤ right) :
    PhysicalWindow.replace (word.cast same) replacement rightFit =
      (PhysicalWindow.replace word replacement leftFit).cast same := by
  cases same
  rfl

private lemma rotate_cast {left right : Nat} (word : BitVec left) (same : left = right) :
    (word.cast same).rotateLeft 1 = (word.rotateLeft 1).cast same := by
  cases same
  rfl

/-- The actual complete Work2 output is the pure packed instruction's entire replacement word. -/
lemma native_secondWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (ArithmeticBlocks.coefficientStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).secondWord =
      (PackedCoefficientWindow.updatedWord state modulus count
        valid conserved active beforeEnd.le).cast
          (CoefficientCapacity.work2_width state modulus valid conserved) := by
  have actual := CoefficientReplacement.native_secondWord modulus.size
    (frame state modulus count valid conserved active beforeEnd iteration) rfl rfl rfl
    (window_fits state modulus valid conserved)
  change (ArithmeticBlocks.coefficientStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).secondWord =
    PhysicalWindow.replace
      ((PackedCoefficientWindow.word state modulus count valid conserved active).cast
        (CoefficientCapacity.work2_width state modulus valid conserved))
      ((SignedCoefficient.addBit
        (CoefficientWindowLaws.targetWord (window state modulus valid conserved)
          (frame state modulus count valid conserved active beforeEnd iteration))
        (CoefficientWindowLaws.sourceWord (window state modulus valid conserved)
          (frame state modulus count valid conserved active beforeEnd iteration))
        (CoefficientPhase.lowBit (CoefficientWindow.current state count).remaining)).setWidth
          (CoefficientWindow.width state)) (window_fits state modulus valid conserved) at actual
  rw [targetWord_eq, sourceWord_eq] at actual
  refine actual.trans ?_
  unfold PackedCoefficientWindow.updatedWord
  rw [PackedCoefficientWindow.signedWindow_eq state modulus count
    valid conserved active beforeEnd.le]
  exact replace_cast _ _ (CoefficientCapacity.work2_width state modulus valid conserved)
    (PackedCoefficientWindow.window_fits state modulus count valid conserved active beforeEnd.le)
    (window_fits state modulus valid conserved)

/-- Literal rotation of the native arithmetic output is exactly the next complete packed payload. -/
lemma native_word_then_rotation (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    BitVec.rotateLeft (ArithmeticBlocks.coefficientStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).secondWord 1 =
      (PackedCoefficientWindow.word state modulus (count + 1) valid conserved active).cast
        (CoefficientCapacity.work2_width state modulus valid conserved) := by
  rw [native_secondWord, rotate_cast,
    PackedCoefficientStep.step_eq_next_word state modulus count valid conserved active beforeEnd.le]

private lemma native_complement (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (CoefficientWindowOrientation.grouping (window state modulus valid conserved)
      (ArithmeticBlocks.coefficientStep modulus.size
        (frame state modulus count valid conserved active beforeEnd iteration))).2 =
      (CoefficientWindowOrientation.grouping (window state modulus valid conserved)
        (frame state modulus count valid conserved active beforeEnd iteration)).2 := by
  rw [ArithmeticBlocks.coefficientStep_eq_source modulus.size _ rfl]
  exact CoefficientBlockLaws.source_complement
    (frame state modulus count valid conserved active beforeEnd iteration) rfl rfl
    (window_fits state modulus valid conserved)

/-- The real guarded post-shift, including Ctrl cleanup, produces the next complete packed Work2. -/
lemma native_postShift_secondWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (GuardedShift.step true (ArithmeticBlocks.coefficientStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration))).secondWord =
      (PackedCoefficientWindow.word state modulus (count + 1) valid conserved active).cast
        (CoefficientCapacity.work2_width state modulus valid conserved) := by
  let original := frame state modulus count valid conserved active beforeEnd iteration
  let after := ArithmeticBlocks.coefficientStep modulus.size original
  have preserved := native_complement state modulus count valid conserved active beforeEnd iteration
  have first := congrArg
    (fun value : ArithmeticWindowRegisters.Complement (window state modulus valid conserved) =>
      value.2.2.2.2.1.1) preserved
  have second := congrArg
    (fun value : ArithmeticWindowRegisters.Complement (window state modulus valid conserved) =>
      value.2.2.2.2.1.2) preserved
  change after.flags.first = true at first
  change after.flags.second = false at second
  have clean : after.control = false :=
    ArithmeticBlocks.coefficientStep_control modulus.size original
  change (GuardedShift.step true after).secondWord = _
  rw [GuardedShift.step_eq_source modulus.size true after clean]
  unfold GuardedShift.sourceStep
  rw [first, if_pos rfl, second]
  change after.secondWord.rotateLeft 1 = _
  exact native_word_then_rotation state modulus count valid conserved active beforeEnd iteration

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientPhaseAction
