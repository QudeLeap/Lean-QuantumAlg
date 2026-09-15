/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Registers
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Native semantic bit lenses and actual shared-EEA placement

Every lens below reads and flips one actual encoded source wire. The
physical order is Work1, Work2, the four finite lengths, and the five
control wires [LYL+26, sec_EEA/sub_regshare.tex:16-26]. Word-wire indices
are big-endian physical positions, matching the mathematical packing
owners. Arithmetic callers can reverse these indices when addressing
little-endian numerical bits.

The two terminal high-counter lenses reuse Work1 positions `n` and
`n+1`. Their physical addresses are proved distinct from the entire
original low-shift register. No new high-counter storage or workspace
is introduced. These lenses and the explicit contiguous placement are
foundations for actual native gate lists, not a completed EEA step or a
resource bound for a whole algorithm.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA

noncomputable section

open BinaryLabelEncoding NumberTheory.SharedEEA

/-- A finite word bit at its actual physical big-endian wire position. -/
def wordBit {width : Nat} (wire : Fin width) : EncodedBit (wordEncoding width) :=
  ofEquivBit BitVec.equivFin.toEquiv wire

theorem wordBit_get {width : Nat} (wire : Fin width) (word : BitVec width) :
    (wordBit wire).get word = word.getMsbD wire.val := by
  change word.toNat.testBit (width - 1 - wire.val) = word.getMsbD wire.val
  simp only [BitVec.getMsbD_eq_getLsbD, wire.isLt, decide_true, Bool.true_and, BitVec.getLsbD]

private def liftWords {width : Nat} (bit : EncodedBit (wordPairEncoding width)) :
    EncodedBit (encoding width) :=
  (prodLeftBit (wordPairEncoding width) (tailEncoding width) bit).relabel
    (registerTupleEquiv width)

private def liftLengths {width : Nat} (bit : EncodedBit (lengthEncoding width)) :
    EncodedBit (encoding width) :=
  (prodRightBit (wordPairEncoding width) (tailEncoding width)
    (prodLeftBit (lengthEncoding width) controlEncoding bit)).relabel (registerTupleEquiv width)

private def liftControl {width : Nat} (bit : EncodedBit controlEncoding) :
    EncodedBit (encoding width) :=
  (prodRightBit (wordPairEncoding width) (tailEncoding width)
    (prodRightBit (lengthEncoding width) controlEncoding bit)).relabel (registerTupleEquiv width)

private def liftFlags {width : Nat} (bit : EncodedBit flagEncoding) :
    EncodedBit (encoding width) :=
  liftControl (prodLeftBit flagEncoding BinaryLabelEncoding.bool bit)

/-- Address one actual physical bit of Work1. -/
def firstWordBit (width : Nat) (wire : Fin (width + 3)) : EncodedBit (encoding width) :=
  liftWords (prodLeftBit (wordEncoding (width + 3)) (wordEncoding (width + 3)) (wordBit wire))

/-- Address one actual physical bit of Work2. -/
def secondWordBit (width : Nat) (wire : Fin (width + 3)) : EncodedBit (encoding width) :=
  liftWords (prodRightBit (wordEncoding (width + 3)) (wordEncoding (width + 3)) (wordBit wire))

/-- Address the coefficient-length register, not the coefficient payload itself. -/
def coefficientLengthBit (width : Nat) (wire : Fin width.size) : EncodedBit (encoding width) :=
  liftLengths (prodLeftBit (lengthPairEncoding width) (lengthPairEncoding width)
    (prodLeftBit (wordEncoding width.size) (wordEncoding width.size) (wordBit wire)))

/-- Address the effective quotient-length register. -/
def quotientLengthBit (width : Nat) (wire : Fin width.size) : EncodedBit (encoding width) :=
  liftLengths (prodLeftBit (lengthPairEncoding width) (lengthPairEncoding width)
    (prodRightBit (wordEncoding width.size) (wordEncoding width.size) (wordBit wire)))

/-- Address the actual divisor-length register used by the terminal predicate. -/
def divisorLengthBit (width : Nat) (wire : Fin width.size) : EncodedBit (encoding width) :=
  liftLengths (prodRightBit (lengthPairEncoding width) (lengthPairEncoding width)
    (prodLeftBit (wordEncoding width.size) (wordEncoding width.size) (wordBit wire)))

/-- Address one bit of the original low shift counter. -/
def shiftBit (width : Nat) (wire : Fin width.size) : EncodedBit (encoding width) :=
  liftLengths (prodRightBit (lengthPairEncoding width) (lengthPairEncoding width)
    (prodRightBit (wordEncoding width.size) (wordEncoding width.size) (wordBit wire)))

def phase1Bit (width : Nat) : EncodedBit (encoding width) :=
  liftFlags (prodLeftBit flagPairEncoding flagPairEncoding
    (prodLeftBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool boolBit))

def phase2Bit (width : Nat) : EncodedBit (encoding width) :=
  liftFlags (prodLeftBit flagPairEncoding flagPairEncoding
    (prodRightBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool boolBit))

def signBit (width : Nat) : EncodedBit (encoding width) :=
  liftFlags (prodRightBit flagPairEncoding flagPairEncoding
    (prodLeftBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool boolBit))

def iterationBit (width : Nat) : EncodedBit (encoding width) :=
  liftFlags (prodRightBit flagPairEncoding flagPairEncoding
    (prodRightBit BinaryLabelEncoding.bool BinaryLabelEncoding.bool boolBit))

/-- The separately declared source Ctrl wire is explicit, rather than hidden workspace. -/
def controlBit (width : Nat) : EncodedBit (encoding width) :=
  liftControl (prodRightBit flagEncoding BinaryLabelEncoding.bool boolBit)

theorem firstWordBit_get (width : Nat) (wire : Fin (width + 3)) (state : Registers width) :
    (firstWordBit width wire).get state = state.firstWord.getMsbD wire.val :=
  wordBit_get wire state.firstWord

theorem secondWordBit_get (width : Nat) (wire : Fin (width + 3)) (state : Registers width) :
    (secondWordBit width wire).get state = state.secondWord.getMsbD wire.val :=
  wordBit_get wire state.secondWord

theorem coefficientLengthBit_get (width : Nat) (wire : Fin width.size) (state : Registers width) :
    (coefficientLengthBit width wire).get state = state.coefficientLength.getMsbD wire.val :=
  wordBit_get wire state.coefficientLength

theorem quotientLengthBit_get (width : Nat) (wire : Fin width.size) (state : Registers width) :
    (quotientLengthBit width wire).get state = state.quotientLength.getMsbD wire.val :=
  wordBit_get wire state.quotientLength

theorem divisorLengthBit_get (width : Nat) (wire : Fin width.size) (state : Registers width) :
    (divisorLengthBit width wire).get state = state.divisorLength.getMsbD wire.val :=
  wordBit_get wire state.divisorLength

theorem shiftBit_get (width : Nat) (wire : Fin width.size) (state : Registers width) :
    (shiftBit width wire).get state = state.shift.getMsbD wire.val :=
  wordBit_get wire state.shift

theorem phase1Bit_get (width : Nat) (state : Registers width) :
    (phase1Bit width).get state = state.flags.first := rfl

theorem phase2Bit_get (width : Nat) (state : Registers width) :
    (phase2Bit width).get state = state.flags.second := rfl

theorem signBit_get (width : Nat) (state : Registers width) :
    (signBit width).get state = state.flags.sign := rfl

theorem iterationBit_get (width : Nat) (state : Registers width) :
    (iterationBit width).get state = state.flags.iteration := rfl

theorem controlBit_get (width : Nat) (state : Registers width) :
    (controlBit width).get state = state.control := rfl

theorem firstWordBit_wire (width : Nat) (wire : Fin (width + 3)) :
    (firstWordBit width wire).wire.val = wire.val := rfl

theorem secondWordBit_wire (width : Nat) (wire : Fin (width + 3)) :
    (secondWordBit width wire).wire.val = width + 3 + wire.val := rfl

theorem coefficientLengthBit_wire (width : Nat) (wire : Fin width.size) :
    (coefficientLengthBit width wire).wire.val = 2 * (width + 3) + wire.val := by
  change ((width + 3) + (width + 3)) + wire.val = _
  omega

theorem quotientLengthBit_wire (width : Nat) (wire : Fin width.size) :
    (quotientLengthBit width wire).wire.val = 2 * (width + 3) + width.size + wire.val := by
  change ((width + 3) + (width + 3)) + (width.size + wire.val) = _
  omega

theorem divisorLengthBit_wire (width : Nat) (wire : Fin width.size) :
    (divisorLengthBit width wire).wire.val = 2 * (width + 3) + 2 * width.size + wire.val := by
  change ((width + 3) + (width + 3)) + ((width.size + width.size) + wire.val) = _
  omega

theorem shiftBit_wire (width : Nat) (wire : Fin width.size) :
    (shiftBit width wire).wire.val = 2 * (width + 3) + 3 * width.size + wire.val := by
  change ((width + 3) + (width + 3)) + ((width.size + width.size) + (width.size + wire.val)) = _
  omega

theorem phase1Bit_wire (width : Nat) :
    (phase1Bit width).wire.val = 2 * (width + 3) + 4 * width.size := by
  change ((width + 3) + (width + 3)) +
    (((width.size + width.size) + (width.size + width.size)) + 0) = _
  omega

theorem phase2Bit_wire (width : Nat) :
    (phase2Bit width).wire.val = 2 * (width + 3) + 4 * width.size + 1 := by
  change ((width + 3) + (width + 3)) +
    (((width.size + width.size) + (width.size + width.size)) + (1 + 0)) = _
  omega

theorem signBit_wire (width : Nat) :
    (signBit width).wire.val = 2 * (width + 3) + 4 * width.size + 2 := by
  change ((width + 3) + (width + 3)) +
    (((width.size + width.size) + (width.size + width.size)) + ((1 + 1) + 0)) = _
  omega

theorem iterationBit_wire (width : Nat) :
    (iterationBit width).wire.val = 2 * (width + 3) + 4 * width.size + 3 := by
  change ((width + 3) + (width + 3)) +
    (((width.size + width.size) + (width.size + width.size)) + ((1 + 1) + (1 + 0))) = _
  omega

theorem controlBit_wire (width : Nat) :
    (controlBit width).wire.val = 2 * (width + 3) + 4 * width.size + 4 := by
  change ((width + 3) + (width + 3)) +
    (((width.size + width.size) + (width.size + width.size)) + (((1 + 1) + (1 + 1)) + 0)) = _
  omega

/-- Reuse the two proved existing Work1 padding positions as semantic high-counter lenses. -/
def paddingBit (width : Nat) (index : Fin 2) : EncodedBit (encoding width) :=
  firstWordBit width ⟨width + index.val, by have bound := index.isLt; omega⟩

/-- At the original modulus width, the lens is exactly the proved terminal padding position. -/
theorem paddingBit_modulus (modulus : Nat) (index : Fin 2) :
    paddingBit modulus.size index =
      firstWordBit modulus.size (TerminalPadding.paddingPosition modulus index) := rfl

theorem paddingBit_wire (width : Nat) (index : Fin 2) :
    (paddingBit width index).wire.val = width + index.val := rfl

/-- The native high-counter lens reads the same exact bit as the proved finite-word clock. -/
theorem paddingBit_get (width : Nat) (index : Fin 2) (state : Registers width) :
    (paddingBit width index).get state = (PaddingClock.high state.firstWord).getMsbD index.val := by
  rw [paddingBit, firstWordBit_get]
  exact PaddingClock.high_bit state.firstWord index.val index.isLt

/-- No terminal high-counter wire aliases any original low-counter wire. -/
theorem paddingBit_shiftBit_ne (width : Nat) (index : Fin 2) (wire : Fin width.size) :
    (paddingBit width index).wire ≠ (shiftBit width wire).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [paddingBit_wire, shiftBit_wire] at values
  have indexBound := index.isLt
  omega

/-- Place precisely the declared source wires at a caller-specified contiguous physical base. -/
def qubitLayout (width base : Nat) : QubitLayout (encoding width).width where
  physical_idx wire := base + wire.val
  physical_idx_injective := by
    intro left right same
    apply Fin.ext
    change base + left.val = base + right.val at same
    omega

/-- The actual finite-dimensional layout contains those same declared dimension-two wires. -/
def quantumLayout (width base : Nat) : QuantumLayout (encoding width).width :=
  (qubitLayout width base).toQuantumLayout

/-- Every semantic lens uses its exact allocated physical identity under the declared placement. -/
theorem qubitLayout_bit_identity (width base : Nat) (bit : EncodedBit (encoding width)) :
    (qubitLayout width base).physical_idx bit.wire = base + bit.wire.val := rfl

/-- The reused high bits occupy the original Work1 identities, with no additional wire. -/
theorem qubitLayout_padding_identity (width base : Nat) (index : Fin 2) :
    (qubitLayout width base).physical_idx (paddingBit width index).wire =
      base + width + index.val := by
  rw [qubitLayout_bit_identity, paddingBit_wire]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA
