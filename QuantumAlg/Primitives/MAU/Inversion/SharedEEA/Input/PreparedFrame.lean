/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Input.Assembly
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.BitValues
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PreparedFrame

/-!
# The actually prepared frame is the literal source initial frame

Every bit of the fresh auxiliary basis comes from the one fixed
`Circuit.prepare` operation. Every old input bit comes from the actual
original quantum register, through equality of its physical wire records.
The exact assembly therefore has the source initial label for every
possible input label [LYL+26, sec_EEA/sub_4phase.tex:104-117].

No input-dependent state is passed to preparation. This proves the basis
identification needed to compose its full joint matrix with the native
fold and length writer. In particular, the field equalities establish
all initial clean control and length conditions internally.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InputPreparedFrame

noncomputable section

open Execution InputPreparation InputAssembly

/-- Decode the actual prepared runtime label through the proved total source binary encoding. -/
def frameEquiv (width : Nat) : (after width).register.Index ≃ Registers width :=
  (InputAssembly.basisEquiv width).trans (PreparedFrame.registerLabelEquiv width).symm

private lemma encode_frameEquiv (width : Nat) (basis : (after width).register.Index) :
    (encoding width).encode (frameEquiv width basis) = InputAssembly.basisEquiv width basis :=
  (PreparedFrame.registerLabelEquiv width).apply_symm_apply _

/-- Source field values at the actual prepared auxiliary basis and original input coordinate. -/
def preparedFrame (modulus : Nat) (old : (before modulus.size).register.Index) :
    Registers modulus.size :=
  frameEquiv modulus.size
    (InputAssembly.assembly modulus.size ((preparation modulus).value, old))

private lemma wireIndex_val {width : Nat} (wire : Fin width) :
    (WireAddress.bitIndex wire).val = wire.rev.val := by
  dsimp only [WireAddress.bitIndex, Fin.rev]
  omega

private lemma prepared_get_auxiliary (modulus : Nat)
    (old : (before modulus.size).register.Index) (bit : EncodedBit (encoding modulus.size))
    (outside : bit.wire.val < prefixWidth modulus.size ∨
      prefixWidth modulus.size + modulus.size ≤ bit.wire.val) :
    bit.get (preparedFrame modulus old) = fixedBit modulus bit.wire.val := by
  rw [← bit.get_eq, wireIndex_val]
  change ((encoding modulus.size).encode (frameEquiv modulus.size
    (InputAssembly.assembly modulus.size ((preparation modulus).value, old)))).val.testBit
      bit.wire.rev.val = _
  rw [encode_frameEquiv]
  have complete := complete_width modulus.size
  have bound := bit.wire.isLt
  obtain ⟨index, position⟩ : ∃ index : Fin (auxiliaryWidth modulus.size),
      auxiliaryPosition modulus.size index = bit.wire := by
    rcases outside with beforeInput | afterInput
    · refine ⟨⟨bit.wire.val, by unfold auxiliaryWidth; omega⟩, ?_⟩
      apply Fin.ext
      change (if bit.wire.val < prefixWidth modulus.size then bit.wire.val
        else modulus.size + bit.wire.val) = bit.wire.val
      rw [if_pos beforeInput]
    · refine ⟨⟨bit.wire.val - modulus.size, by omega⟩, ?_⟩
      apply Fin.ext
      change (if bit.wire.val - modulus.size < prefixWidth modulus.size
        then bit.wire.val - modulus.size
        else modulus.size + (bit.wire.val - modulus.size)) = bit.wire.val
      rw [if_neg (by omega)]
      omega
  have actual := basisEquiv_prepared_auxiliary modulus old index
  rw [position] at actual
  exact actual.trans (congrArg (fixedBit modulus) (congrArg Fin.val position))

private lemma prepared_get_input (modulus : Nat)
    (old : (before modulus.size).register.Index) (bit : EncodedBit (encoding modulus.size))
    (index : Fin modulus.size) (position : bit.wire = inputPosition modulus.size index) :
    bit.get (preparedFrame modulus old) =
      (inputBasisEquiv modulus.size old).val.testBit index.rev.val := by
  rw [← bit.get_eq, wireIndex_val]
  change ((encoding modulus.size).encode (frameEquiv modulus.size
    (InputAssembly.assembly modulus.size ((preparation modulus).value, old)))).val.testBit
      bit.wire.rev.val = _
  rw [encode_frameEquiv, position]
  exact basisEquiv_input modulus.size (preparation modulus).value old index

private lemma registers_ext {width : Nat} {left right : Registers width}
    (first : left.firstWord = right.firstWord) (second : left.secondWord = right.secondWord)
    (coefficient : left.coefficientLength = right.coefficientLength)
    (quotient : left.quotientLength = right.quotientLength)
    (divisor : left.divisorLength = right.divisorLength) (shift : left.shift = right.shift)
    (flags : left.flags = right.flags) (control : left.control = right.control) : left = right := by
  cases left
  cases right
  cases first
  cases second
  cases coefficient
  cases quotient
  cases divisor
  cases shift
  cases flags
  cases control
  rfl

/-- All actual prepared fields equal the source initial frame on the original input label. -/
lemma preparedFrame_eq_initial (modulus : Nat) (old : (before modulus.size).register.Index) :
    preparedFrame modulus old =
      InitialFrame.initial modulus (inputBasisEquiv modulus.size old) := by
  apply registers_ext
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin (modulus.size + 3) := ⟨index, within⟩
    have actual := prepared_get_auxiliary modulus old (firstWordBit modulus.size selected)
      (Or.inl (by
        rw [firstWordBit_wire]
        change index < prefixWidth modulus.size
        unfold prefixWidth
        omega))
    have expected := InitialBitValues.firstWord_fixed modulus (inputBasisEquiv modulus.size old)
      selected
    rw [firstWordBit_get] at actual expected
    exact actual.trans expected
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin (modulus.size + 3) := ⟨index, within⟩
    by_cases padding : index < 3
    · have actual := prepared_get_auxiliary modulus old (secondWordBit modulus.size selected)
        (Or.inl (by
          rw [secondWordBit_wire]
          change modulus.size + 3 + index < prefixWidth modulus.size
          unfold prefixWidth
          omega))
      have expected := InitialBitValues.secondWord_padding_fixed modulus
        (inputBasisEquiv modulus.size old) selected padding
      rw [secondWordBit_get] at actual expected
      exact actual.trans expected
    · let inputIndex : Fin modulus.size := ⟨index - 3, by omega⟩
      have actual := prepared_get_input modulus old (secondWordBit modulus.size selected)
        inputIndex (by
          apply Fin.ext
          rw [secondWordBit_wire]
          change modulus.size + 3 + index = prefixWidth modulus.size + (index - 3)
          unfold prefixWidth
          omega)
      have expected := InitialBitValues.secondWord_input modulus
        (inputBasisEquiv modulus.size old) inputIndex
      rw [secondWordBit_get] at actual expected
      have sameIndex : 3 + inputIndex.val = index := by change 3 + (index - 3) = index; omega
      change (InitialFrame.initial modulus (inputBasisEquiv modulus.size old)).secondWord.getMsbD
        (3 + inputIndex.val) = _ at expected
      rw [sameIndex] at expected
      exact actual.trans expected.symm
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin modulus.size.size := ⟨index, within⟩
    have actual := prepared_get_auxiliary modulus old (coefficientLengthBit modulus.size selected)
      (Or.inr (by
        rw [coefficientLengthBit_wire]
        unfold prefixWidth
        omega))
    have expected := InitialBitValues.coefficientLength_fixed modulus
      (inputBasisEquiv modulus.size old) selected
    rw [coefficientLengthBit_get] at actual expected
    exact actual.trans expected
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin modulus.size.size := ⟨index, within⟩
    have actual := prepared_get_auxiliary modulus old (quotientLengthBit modulus.size selected)
      (Or.inr (by
        rw [quotientLengthBit_wire]
        unfold prefixWidth
        omega))
    have expected := InitialBitValues.quotientLength_fixed modulus
      (inputBasisEquiv modulus.size old) selected
    rw [quotientLengthBit_get] at actual expected
    exact actual.trans expected
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin modulus.size.size := ⟨index, within⟩
    have actual := prepared_get_auxiliary modulus old (divisorLengthBit modulus.size selected)
      (Or.inr (by
        rw [divisorLengthBit_wire]
        unfold prefixWidth
        omega))
    have expected := InitialBitValues.divisorLength_fixed modulus
      (inputBasisEquiv modulus.size old) selected
    rw [divisorLengthBit_get] at actual expected
    exact actual.trans expected
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin modulus.size.size := ⟨index, within⟩
    have actual := prepared_get_auxiliary modulus old (shiftBit modulus.size selected)
      (Or.inr (by
        rw [shiftBit_wire]
        unfold prefixWidth
        omega))
    have expected := InitialBitValues.shift_fixed modulus
      (inputBasisEquiv modulus.size old) selected
    rw [shiftBit_get] at actual expected
    exact actual.trans expected
  · apply NumberTheory.SharedEEA.PhaseControl.Flags.ext
    · exact (prepared_get_auxiliary modulus old (phase1Bit modulus.size)
        (Or.inr (by rw [phase1Bit_wire]; unfold prefixWidth; omega))).trans
          (InitialBitValues.phase1_fixed modulus (inputBasisEquiv modulus.size old))
    · exact (prepared_get_auxiliary modulus old (phase2Bit modulus.size)
        (Or.inr (by rw [phase2Bit_wire]; unfold prefixWidth; omega))).trans
          (InitialBitValues.phase2_fixed modulus (inputBasisEquiv modulus.size old))
    · exact (prepared_get_auxiliary modulus old (signBit modulus.size)
        (Or.inr (by rw [signBit_wire]; unfold prefixWidth; omega))).trans
          (InitialBitValues.sign_fixed modulus (inputBasisEquiv modulus.size old))
    · exact (prepared_get_auxiliary modulus old (iterationBit modulus.size)
        (Or.inr (by rw [iterationBit_wire]; unfold prefixWidth; omega))).trans
          (InitialBitValues.iteration_fixed modulus (inputBasisEquiv modulus.size old))
  · exact (prepared_get_auxiliary modulus old (controlBit modulus.size)
      (Or.inr (by rw [controlBit_wire]; unfold prefixWidth; omega))).trans
        (InitialBitValues.control_fixed modulus (inputBasisEquiv modulus.size old))

/-- The exact actual prepared binary label is the source initial label on the original input. -/
lemma basisEquiv_prepared_initial (modulus : Nat)
    (old : (before modulus.size).register.Index) :
    InputAssembly.basisEquiv modulus.size
        (InputAssembly.assembly modulus.size ((preparation modulus).value, old)) =
      (encoding modulus.size).encode
        (InitialFrame.initial modulus (inputBasisEquiv modulus.size old)) := by
  rw [← encode_frameEquiv]
  change (encoding modulus.size).encode (preparedFrame modulus old) = _
  rw [preparedFrame_eq_initial]

end

end QuantumAlg.MAU.Inversion.SharedEEA.InputPreparedFrame
