/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Phase.Packing
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Retained

/-!
# Actual phase-three quotient-bit consumption

The source exchanges Sign with the last currently retained quotient bit,
then decrements the quotient length [LYL+26, sec_EEA/sub_regshare.tex:288-296;
LYL+26, sec_EEA/sub_opt.tex:52-59]. For Phase1 one this physical position is
exactly the untruncated natural sum of coefficient and quotient lengths.
The actual selected Sign receives the old bit, while the old Sign is
written at that same position before the field boundary changes.

These laws specialize the existing native selector and quotient program.
They preserve the complete prefix, lower remainder, Work2, divisor/shift
lengths, phases, Iter, and Ctrl. The eventual trajectory establishes the
local position and clean Sign/Control invariants internally; no new caller
assumption or alternate execution rule is introduced.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientExchange

noncomputable section

private lemma selected_source (width : Nat) (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat < width + 3) :
    SelectionSchedule.sourceStep width state = SelectionSwap.exchange width
      ⟨state.coefficientLength.toNat + state.quotientLength.toNat, within⟩ state := by
  unfold SelectionSchedule.sourceStep
  simp only [first, if_true, Nat.add_zero, dif_pos within, SelectionKey.phaseSelected,
    second, Bool.true_xor, Bool.not_false]

/-- The actual phase-three quotient program subtracts one from the retained finite length. -/
lemma source_quotientLength (width : Nat) (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat < width + 3) :
    (SignQuotient.sourceStep width state).quotientLength = state.quotientLength - 1 := by
  let selected : Fin (width + 3) :=
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat, within⟩
  have retained := SignQuotientFields.exchange_fields width selected state
  have firstSame := retained.2.2.1.trans first
  have secondSame := retained.2.2.2.trans second
  unfold SignQuotient.sourceStep
  rw [selected_source width state first second within]
  change (if PhaseQuotient.condition (SelectionSwap.exchange width selected state) then
      if (SelectionSwap.exchange width selected state).flags.first then
        (SelectionSwap.exchange width selected state).quotientLength - 1
      else (SelectionSwap.exchange width selected state).quotientLength + 1
    else (SelectionSwap.exchange width selected state).quotientLength) = _
  simp only [PhaseQuotient.condition, firstSame, secondSame, Bool.true_xor, Bool.not_false,
    if_true, retained.2.1]

/-- The actual selected original quotient coordinate becomes Sign before coefficient arithmetic. -/
lemma source_sign (width : Nat) (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat < width + 3) :
    (SignQuotient.sourceStep width state).flags.sign =
      state.firstWord.getMsbD (state.coefficientLength.toNat + state.quotientLength.toNat) := by
  unfold SignQuotient.sourceStep
  rw [selected_source width state first second within]
  exact SelectionSwap.exchange_sign width
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat, within⟩ state

/-- The old Sign is placed above the entire original remainder when its field expands by one bit. -/
lemma source_low (width : Nat) (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat < width + 3) :
    let position := state.coefficientLength.toNat + state.quotientLength.toNat
    (SignQuotient.sourceStep width state).firstWord.setWidth (width + 3 - 1 - position + 1) =
      BitVec.cons state.flags.sign (state.firstWord.setWidth (width + 3 - 1 - position)) := by
  dsimp only
  unfold SignQuotient.sourceStep
  rw [selected_source width state first second within]
  exact RemainderExchange.exchange_word width
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat, within⟩ state

/-- Every actual coefficient, separator, and remaining higher quotient bit is retained. -/
lemma source_prefix (width : Nat) (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat < width + 3) :
    let position := state.coefficientLength.toNat + state.quotientLength.toNat
    (SignQuotient.sourceStep width state).firstWord.extractLsb'
        (width + 3 - 1 - position + 1) position =
      state.firstWord.extractLsb' (width + 3 - 1 - position + 1) position := by
  dsimp only
  unfold SignQuotient.sourceStep
  rw [selected_source width state first second within]
  exact RemainderPhasePacking.exchange_prefix width
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat, within⟩ state

/-- The actual source consumes only its quotient bit and length, preserving every other field. -/
lemma source_retained (width : Nat) (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat < width + 3) :
    (SignQuotient.sourceStep width state).secondWord = state.secondWord ∧
      (SignQuotient.sourceStep width state).coefficientLength = state.coefficientLength ∧
      (SignQuotient.sourceStep width state).divisorLength = state.divisorLength ∧
      (SignQuotient.sourceStep width state).shift = state.shift ∧
      (SignQuotient.sourceStep width state).flags.first = true ∧
      (SignQuotient.sourceStep width state).flags.second = false ∧
      (SignQuotient.sourceStep width state).flags.iteration = state.flags.iteration ∧
      (SignQuotient.sourceStep width state).control = state.control := by
  let selected : Fin (width + 3) :=
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat, within⟩
  have retained := SignQuotientFields.exchange_fields width selected state
  unfold SignQuotient.sourceStep
  rw [selected_source width state first second within]
  exact ⟨SignQuotient.exchange_secondWord width selected state, retained.1,
    RemainderRetained.exchange_length width selected .divisor state,
    RemainderRetained.exchange_length width selected .shift state,
    retained.2.2.1.trans first, retained.2.2.2.trans second,
    RemainderRetained.exchange_iteration width selected state,
    SelectionSwap.exchange_control width selected state⟩

/-- Native initialized control executes this real quotient-bit read and finite decrement jointly. -/
lemma native_sign_and_length (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true)
    (second : state.flags.second = false)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat < width + 3) :
    (SignQuotient.step width state).flags.sign =
        state.firstWord.getMsbD (state.coefficientLength.toNat + state.quotientLength.toNat) ∧
      (SignQuotient.step width state).quotientLength = state.quotientLength - 1 := by
  rw [SignQuotient.step_eq_sourceStep width state clean]
  exact ⟨source_sign width state first second within,
    source_quotientLength width state first second within⟩

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientExchange
