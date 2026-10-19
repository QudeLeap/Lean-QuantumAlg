/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.SignQuotient.Fields

/-!
# Complete retained fields of actual division arithmetic and quotient exchange

The source's signed remainder arithmetic reads Work2, and the subsequent
Sign selector uses that same word as dirty conjunction work. Both actual
programs return every Work2 bit, including its wrapped coefficient suffix
[LYL+26, sec_EEA/sub_regshare.tex:263-287; LYL+26, sec_EEA/sub_opt.tex:43-59].
The selector also retains the actual divisor and shift lengths and Iter.
These statements follow the existing gate programs and physical bit
coordinates, not an abstract replacement of their work registers.

All equalities retain complete finite words and arbitrary original
values. The source-specialized conditions are internal phase trajectory
invariants. No separability, zero suffix, zero borrowed work, or additional
condition on the eventual EEA input is introduced.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.RemainderRetained

noncomputable section

open EncodedBit ArithmeticWindowRegisters ArithmeticWindowLaws

private lemma arithmetic_secondWord {width : Nat} (selected : Window width)
    (operation : ArithmeticWindowProgram.Operation) (state : Registers width) :
    (ArithmeticWindowProgram.step selected operation state).secondWord = state.secondWord := by
  have outside := congrArg (fun value : Complement selected => value.2.1)
    (step_complement selected operation state)
  change ((wordEquiv selected
      (ArithmeticWindowProgram.step selected operation state).secondWord).1,
      (wordEquiv selected
        (ArithmeticWindowProgram.step selected operation state).secondWord).2.2) =
    ((wordEquiv selected state.secondWord).1, (wordEquiv selected state.secondWord).2.2) at outside
  apply (wordEquiv selected).injective
  exact Prod.ext
    (congrArg (fun pair : BitVec selected.above × BitVec selected.below => pair.1) outside)
    (Prod.ext (step_sourceWord selected operation state)
      (congrArg (fun pair : BitVec selected.above × BitVec selected.below => pair.2) outside))

/-- Actual signed subtraction, Sign complement, and conditional add-back retain all of Work2. -/
lemma source_secondWord {width : Nat} (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    (ArithmeticBlocks.remainderSource state).secondWord = state.secondWord := by
  by_cases divisor : state.divisorLength ≠ 0
  · rw [RemainderBlockLaws.source_eq state first second divisor fits]
    split
    · exact (arithmetic_secondWord _ .addLow _).trans
        (arithmetic_secondWord _ .subtractSigned state)
    · exact arithmetic_secondWord _ .subtractSigned state
  · rw [RemainderBlockLaws.source_finished state (Classical.not_not.mp divisor)]
    rfl

/-- The emitted native remainder program returns the whole original source word. -/
lemma native_secondWord (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    (ArithmeticBlocks.remainderStep width state).secondWord = state.secondWord := by
  rw [ArithmeticBlocks.remainderStep_eq_source width state clean]
  exact source_secondWord state first second fits

private lemma exchange_length (width : Nat) (selected : Fin (width + 3))
    (field : PredicateLayout.LengthField) (state : Registers width) :
    PredicateLayout.lengthValue field (SelectionSwap.exchange width selected state) =
      PredicateLayout.lengthValue field state := by
  apply BitVec.eq_of_getMsbD_eq
  intro bit within
  let observed := PredicateLayout.lengthBit width field ⟨bit, within⟩
  have signDifferent : (signBit width).wire ≠ observed.wire := by
    intro same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    change (signBit width).wire.val =
      (PredicateLayout.lengthBit width field ⟨bit, within⟩).wire.val at values
    rw [signBit_wire, PredicateLayout.lengthBit_wire] at values
    cases field <;> simp only [PredicateLayout.lengthOffset] at values <;> omega
  have targetDifferent : (firstWordBit width selected).wire ≠ observed.wire := by
    intro same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    change (firstWordBit width selected).wire.val =
      (PredicateLayout.lengthBit width field ⟨bit, within⟩).wire.val at values
    rw [firstWordBit_wire, PredicateLayout.lengthBit_wire] at values
    have selectedBound := selected.isLt
    omega
  exact (PredicateLayout.lengthBit_get width field ⟨bit, within⟩ _).symm.trans
    ((swapStep_get_observed_of_swap_ne (signBit width) (firstWordBit width selected)
      observed (SelectionSwap.sign_word width selected) signDifferent targetDifferent state).trans
        (PredicateLayout.lengthBit_get width field ⟨bit, within⟩ state))

private lemma exchange_iteration (width : Nat) (selected : Fin (width + 3))
    (state : Registers width) :
    (SelectionSwap.exchange width selected state).flags.iteration = state.flags.iteration := by
  have signDifferent : (signBit width).wire ≠ (iterationBit width).wire := by
    intro same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    rw [signBit_wire, iterationBit_wire] at values
    omega
  have targetDifferent : (firstWordBit width selected).wire ≠ (iterationBit width).wire := by
    intro same
    have values := congrArg (fun index : Fin (encoding width).width => index.val) same
    rw [firstWordBit_wire, iterationBit_wire] at values
    have selectedBound := selected.isLt
    omega
  exact swapStep_get_observed_of_swap_ne (signBit width) (firstWordBit width selected)
    (iterationBit width) (SelectionSwap.sign_word width selected)
    signDifferent targetDifferent state

/-- Actual phase-two Sign exchange and quotient increment retain divisor, shift, and Iter. -/
lemma source_extra (width : Nat) (state : Registers width)
    (first : state.flags.first = false) (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    (SignQuotient.sourceStep width state).divisorLength = state.divisorLength ∧
      (SignQuotient.sourceStep width state).shift = state.shift ∧
        (SignQuotient.sourceStep width state).flags.iteration = state.flags.iteration := by
  unfold SignQuotient.sourceStep
  rw [RemainderExchange.selected_source width state first second within]
  let selected : Fin (width + 3) :=
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat + 1, within⟩
  exact ⟨exchange_length width selected .divisor state,
    exchange_length width selected .shift state, exchange_iteration width selected state⟩

/-- The actual native selector and quotient program preserve the same complete retained fields. -/
lemma native_extra (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    (SignQuotient.step width state).divisorLength = state.divisorLength ∧
      (SignQuotient.step width state).shift = state.shift ∧
        (SignQuotient.step width state).flags.iteration = state.flags.iteration := by
  rw [SignQuotient.step_eq_sourceStep width state clean]
  exact source_extra width state first second within

/-- Arithmetic and the complete subsequent selector return all original Work2 coordinates. -/
lemma division_secondWord (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true)
    (fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat ≤
      width + 3) :
    (SignQuotient.step width (ArithmeticBlocks.remainderStep width state)).secondWord =
      state.secondWord :=
  (SignQuotient.step_secondWord width _).trans
    (native_secondWord width state clean first second fits)

end

end QuantumAlg.MAU.Inversion.SharedEEA.RemainderRetained
