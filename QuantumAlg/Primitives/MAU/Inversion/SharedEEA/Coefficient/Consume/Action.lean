/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Exchange
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Consume.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Division.Advance

/-!
# Actual quotient consumption reaches the complete coefficient arithmetic frame

The existing `SignQuotient.step` executes the actual selected exchange and
finite quotient decrement before coefficient arithmetic
[LYL+26, sec_EEA/sub_regshare.tex:288-296; LYL+26, sec_EEA/sub_opt.tex:52-67].
The whole original Work1 becomes the next shorter quotient packing with an
explicit new leading remainder zero. Sign receives the actual consumed
quotient bit, while every other original field is retained.

The concluding theorem identifies all fields with the already established
`CoefficientPhaseFrame.frame`, so its existing native arithmetic and
rotation theorems apply to an actually reached state. All position and
no-wrap evidence is supplied by the internal source-domain construction.
No caller supplies a fit/clean-work promise or an alternate execution rule.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientConsumeAction

noncomputable section

open NumberTheory.SharedEEA CoefficientConsumeFrame

private lemma native_clearedWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (SignQuotient.step modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).firstWord =
        CoefficientPackedStep.clearedWord state modulus count valid conserved beforeEnd := by
  let original := frame state modulus count valid conserved active beforeEnd iteration
  let selected := position state modulus count valid conserved
  have selectedValue : original.coefficientLength.toNat + original.quotientLength.toNat =
      selected.val := (position_val state modulus count
        valid conserved active beforeEnd iteration).symm
  have fits : original.coefficientLength.toNat + original.quotientLength.toNat <
      modulus.size + 3 := selectedValue.symm ▸ selected.isLt
  rw [SignQuotient.step_eq_sourceStep modulus.size original rfl]
  let output := SignQuotient.sourceStep modulus.size original
  have prefixEq := CoefficientExchange.source_prefix modulus.size original rfl rfl fits
  have lowEq := CoefficientExchange.source_low modulus.size original rfl rfl fits
  dsimp only at prefixEq lowEq
  rw [selectedValue] at prefixEq lowEq
  have prefixNat := (congrArg BitVec.toNat prefixEq).trans
    (firstWord_prefix state modulus count valid conserved active beforeEnd iteration)
  have lowNat := congrArg BitVec.toNat lowEq
  change (output.firstWord.setWidth (modulus.size + 3 - 1 - selected.val + 1)).toNat =
    (BitVec.cons false
      (original.firstWord.setWidth (modulus.size + 3 - 1 - selected.val))).toNat at lowNat
  rw [BitVec.toNat_cons', Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_add] at lowNat
  have remainderNat := lowNat.trans
    (firstWord_low state modulus count valid conserved active beforeEnd iteration)
  have complete : selected.val + (modulus.size + 3 - 1 - selected.val + 1) = modulus.size + 3 := by
    have within := selected.isLt
    omega
  apply BitVec.eq_of_toNat_eq
  calc
    output.firstWord.toNat = _ := RemainderPhasePacking.full_word_toNat output.firstWord complete
    _ = (CoefficientPackedStep.retainedPrefix state modulus count valid conserved).toNat *
        2 ^ (modulus.size + 3 - 1 - selected.val + 1) + state.remainder % state.divisor := by
      rw [prefixNat, remainderNat]
    _ = (CoefficientPackedStep.clearedWord state modulus count
        valid conserved beforeEnd).toNat := by
      unfold CoefficientPackedStep.clearedWord
      rw [BitVec.toNat_cast, DivisionPackedStep.append_toNat, BitVec.toNat_cons',
        Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_add]
      change (CoefficientPackedStep.retainedPrefix state modulus count valid conserved).toNat *
          2 ^ (modulus.size + 3 - 1 - selected.val + 1) + state.remainder % state.divisor =
        (CoefficientPackedStep.retainedPrefix state modulus count valid conserved).toNat *
          2 ^ (CoefficientCapacity.work1RemainderWidth state modulus count + 1) +
            state.remainder % state.divisor
      exact congrArg (fun length =>
        (CoefficientPackedStep.retainedPrefix state modulus count valid conserved).toNat *
          2 ^ (length + 1) + state.remainder % state.divisor)
        (position_lowWidth state modulus count valid conserved)

/-- The actual whole Work1 reaches the existing coefficient-arithmetic frame after consumption. -/
lemma native_firstWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (SignQuotient.step modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).firstWord =
        (CoefficientPhaseFrame.frame state modulus count
          valid conserved active beforeEnd iteration).firstWord :=
  (native_clearedWord state modulus count valid conserved active beforeEnd iteration).trans
    (CoefficientPackedStep.clearedWord_eq_next state modulus count valid conserved beforeEnd)

/-- Actual Sign contains precisely the low quotient digit required by the next arithmetic block. -/
lemma native_sign (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    (SignQuotient.step modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).flags.sign =
        CoefficientPhase.lowBit (CoefficientWindow.current state count).remaining := by
  let original := frame state modulus count valid conserved active beforeEnd iteration
  let selected := position state modulus count valid conserved
  have selectedValue := (position_val state modulus count
    valid conserved active beforeEnd iteration).symm
  have fits : original.coefficientLength.toNat + original.quotientLength.toNat <
      modulus.size + 3 := selectedValue.symm ▸ selected.isLt
  have actual := (CoefficientExchange.native_sign_and_length modulus.size original
    rfl rfl rfl fits).1
  exact actual.trans ((congrArg original.firstWord.getMsbD selectedValue).trans
    (firstWord_digit state modulus count valid conserved active beforeEnd iteration))

/-- Existing native quotient consumption reaches all fields of the coefficient arithmetic frame. -/
lemma native_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    SignQuotient.step modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration) =
        CoefficientPhaseFrame.frame state modulus count
          valid conserved active beforeEnd iteration := by
  let original := frame state modulus count valid conserved active beforeEnd iteration
  let output := SignQuotient.step modulus.size original
  let expected := CoefficientPhaseFrame.frame state modulus count
    valid conserved active beforeEnd iteration
  have selectedValue := (position_val state modulus count
    valid conserved active beforeEnd iteration).symm
  have fits : original.coefficientLength.toNat + original.quotientLength.toNat <
      modulus.size + 3 := selectedValue.symm ▸ (position state modulus count valid conserved).isLt
  have source := SignQuotient.step_eq_sourceStep modulus.size original rfl
  have retained := CoefficientExchange.source_retained modulus.size original rfl rfl fits
  rw [← source] at retained
  have quotient := (CoefficientExchange.native_sign_and_length modulus.size original
    rfl rfl rfl fits).2
  apply Registers.ext_fields output expected
  · exact native_firstWord state modulus count valid conserved active beforeEnd iteration
  · exact retained.1
  · exact retained.2.1
  · exact quotient.trans
      (quotientLength_subtract state modulus count valid conserved active beforeEnd iteration)
  · exact retained.2.2.1
  · exact retained.2.2.2.1
  · exact retained.2.2.2.2.1
  · exact retained.2.2.2.2.2.1
  · exact native_sign state modulus count valid conserved active beforeEnd iteration
  · exact retained.2.2.2.2.2.2.1
  · exact retained.2.2.2.2.2.2.2

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientConsumeAction
