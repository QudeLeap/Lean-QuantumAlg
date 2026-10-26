/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Multiplier
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Operands
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Arithmetic
import all QuantumAlg.Components.Encoded.BitGates.Word.CopyValue

/-!
# Paid square multiplier copy into an existing original clean word

The original source is XORed into the original retained multiplier word.
The accumulator, every flag and the entire remaining caller frame are kept
exactly. No word is allocated. The two copy directions each pay 256 CNOTs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Square

noncomputable section

open QuantumAlg.EncodedBit GateSpec Horner

variable {Rest : Type} (rest : BinaryLabelEncoding Rest)

abbrev savedEncoding : BinaryLabelEncoding (Word × Rest) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width) rest

def multiplier : RetainedMultiplier (savedEncoding rest) where
  value := Prod.fst
  bits := fun index => BinaryLabelEncoding.prodLeftBit (BinaryLabelEncoding.finIdentity width)
    rest (BinaryLabelEncoding.finIdentityBit width (WireAddress.littleEndianWire index))
  reads := by
    intro retained index
    change retained.1.val.testBit
      (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
    rw [WireAddress.bitIndex_littleEndianWire]

def outerBit (outer : EncodedBit rest) : EncodedBit (savedEncoding rest) :=
  BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.finIdentity width) rest outer

lemma outer_multiplier_ne (outer : EncodedBit rest) (index : Fin width) :
    (operandSavedBit (savedEncoding rest) (outerBit rest outer)).wire ≠
      (operandMultiplierBit (savedEncoding rest)
        (.retained ((multiplier rest).bits index))).wire := by
  intro same
  have positions := congrArg Fin.val same
  change 515 + (width + outer.wire.val) = 515 + (width - 1 - index.val) at positions
  have bounded := index.isLt
  omega

def sourceWord : EncodedBit.Word (operandEncoding (savedEncoding rest)) width :=
  ⟨operandSourceBit (savedEncoding rest)⟩

def targetWord : EncodedBit.Word (operandEncoding (savedEncoding rest)) width :=
  ⟨fun index => operandSavedBit (savedEncoding rest) ((multiplier rest).bits index)⟩

private lemma target_distinct (left right : Fin width) (different : left ≠ right) :
    ((targetWord rest).bit left).wire ≠ ((targetWord rest).bit right).wire := by
  intro same
  apply different
  apply Fin.ext
  have positions := congrArg Fin.val same
  change 515 + (width - 1 - left.val) = 515 + (width - 1 - right.val) at positions
  have leftBound := left.isLt
  have rightBound := right.isLt
  omega

private lemma source_target_ne (left right : Fin width) :
    ((sourceWord rest).bit left).wire ≠ ((targetWord rest).bit right).wire := by
  intro same
  have positions := congrArg Fin.val same
  change 256 - 1 - left.val = 515 + (256 - 1 - right.val) at positions
  omega

def copyGates : List (GateSpec (operandEncoding (savedEncoding rest))) :=
  EncodedBit.Word.xorIntoGates (sourceWord rest) (targetWord rest)
    (fun index => source_target_ne rest index index)

def copyProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding (savedEncoding rest)).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (copyGates rest)

/-- Actual paid copy preserves the entire arbitrary accumulator/flag/caller complement. -/
lemma copy_clean (frame : ModularAddition.Controlled.SelectedRegisters) (retained : Rest) :
    stepList (copyGates rest) (frame, (zeroWord, retained)) =
      (frame, (frame.1.1.1, retained)) := by
  exact EncodedBit.Word.xorIntoStep_eq_set_of_clean
    (sourceWord rest) (targetWord rest) (fun index => source_target_ne rest index index)
    (fun state => state.2.1)
    (fun state => (state.1, state.2.2))
    (fun retained word => (retained.1, (word, retained.2))) (fun _ => rfl)
    (by
      intro index state
      change state.2.1.val.testBit
        (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
      rw [WireAddress.bitIndex_littleEndianWire])
    (target_distinct rest) (fun sourceIndex targetIndex =>
      (source_target_ne rest sourceIndex targetIndex).symm)
    (fun _ _ => rfl) (frame, (zeroWord, retained)) frame.1.1.1
    (by apply Fin.ext; simp only [zeroWord, Fin.val_zero])
    (fun index => operandSourceBit_get (savedEncoding rest) index _)

def uncopyGates : List (GateSpec (operandEncoding (savedEncoding rest))) :=
  (copyGates rest).reverse

def uncopyProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding (savedEncoding rest)).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (uncopyGates rest)

/-- The complete literal inverse clears the existing copy word for any current accumulator. -/
lemma uncopy_clean (frame : ModularAddition.Controlled.SelectedRegisters) (retained : Rest) :
    stepList (uncopyGates rest) (frame, (frame.1.1.1, retained)) =
      (frame, (zeroWord, retained)) :=
  (congrArg (stepList (uncopyGates rest)) (copy_clean rest frame retained)).symm.trans
    (stepList_reverse_stepList (copyGates rest) (frame, (zeroWord, retained)))

/-- Copying on original quantum ports retains all phases of the supplied complete frame. -/
lemma copy_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding (savedEncoding rest)) (copyProgram rest) environment
      (stepList (copyGates rest)) :=
  realizesList (QubitLayout.canonical _) .empty (copyGates rest) environment

lemma uncopy_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding (savedEncoding rest)) (uncopyProgram rest) environment
      (stepList (uncopyGates rest)) :=
  realizesList (QubitLayout.canonical _) .empty (uncopyGates rest) environment

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Square
