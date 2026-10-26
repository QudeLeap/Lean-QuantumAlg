/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Controlled.Program

/-!
# Original quantum multiplier ports beside the selected arithmetic frame

The retained caller component can contain the multiplier word, the outer
selector and any other original systems. A multiplier bit can instead be
one of the original addend bits. No register is allocated and no quantum
operand is read into classical storage to select a different program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

abbrev OperandRegisters (Saved : Type) := Controlled.SelectedRegisters × Saved

abbrev operandEncoding {Saved : Type} (saved : BinaryLabelEncoding Saved) :
    BinaryLabelEncoding (OperandRegisters Saved) :=
  BinaryLabelEncoding.prod Controlled.selectorEncoding saved

/-- Static original-port choice: an addend bit or one bit of the retained caller frame. -/
inductive MultiplierPort {Saved : Type} (saved : BinaryLabelEncoding Saved) where
  | addend (index : Fin width)
  | retained (bit : EncodedBit saved)

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)

/-- An addend bit retains its original physical source address through both product frames. -/
def operandSourceBit (index : Fin width) : EncodedBit (operandEncoding saved) :=
  BinaryLabelEncoding.prodLeftBit Controlled.selectorEncoding saved
    (BinaryLabelEncoding.prodLeftBit encoding
      (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool)
      (addendBit index))

/-- The conjunction uses the original selected-add selector, rather than a newly allocated bit. -/
def operandLatchBit : EncodedBit (operandEncoding saved) :=
  BinaryLabelEncoding.prodLeftBit Controlled.selectorEncoding saved Controlled.selectorBit

/-- Every retained caller bit is a real original wire, including the outer selector. -/
def operandSavedBit (bit : EncodedBit saved) : EncodedBit (operandEncoding saved) :=
  BinaryLabelEncoding.prodRightBit Controlled.selectorEncoding saved bit

/-- The chosen multiplier bit is an actual quantum source bit in the full physical frame. -/
def operandMultiplierBit : MultiplierPort saved → EncodedBit (operandEncoding saved)
  | .addend index => operandSourceBit saved index
  | .retained bit => operandSavedBit saved bit

/-- The source readout is little-endian, in the same order as the native arithmetic ports. -/
lemma operandSourceBit_get (index : Fin width) (state : OperandRegisters Saved) :
    (operandSourceBit saved index).get state = state.1.1.1.1.val.testBit index.val := by
  change (MAU.Addition.TTK.leftBit width index).get state.1.1.1 = _
  exact MAU.Addition.TTK.ttkLeftBit_get width index state.1.1.1

/-- The original clean conjunction latch is exactly the selected-add control coordinate. -/
lemma operandLatchBit_get (state : OperandRegisters Saved) :
    (operandLatchBit saved).get state = state.1.2.1 := rfl

/-- Literal selected-add instructions are emitted on the original prefix positions. -/
def operandAdditionGates : List (GateSpec (operandEncoding saved)) :=
  Controlled.controlledAdditionGates.map (GateSpec.prodLeft saved)

def operandAdditionProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (operandAdditionGates saved)

/-- Full raw execution retains every caller coordinate beside the actual native addition. -/
lemma operandAdditionGates_step (state : OperandRegisters Saved) :
    stepList (operandAdditionGates saved) state =
      (Controlled.controlledAdditionStep state.1, state.2) := by
  rw [operandAdditionGates, stepList_prodLeft]
  rfl

/-- Both quantum operands and every flag have their exact original clean-branch outputs. -/
lemma operandAddition_clean_canonical (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (selected : Bool) (retained : Saved) :
    stepList (operandAdditionGates saved)
        ((((source, target), false), (selected, false)), retained) =
      ((((source, if selected then modularSumWord source target else target), false),
        (selected, false)), retained) := by
  rw [operandAdditionGates_step,
    Controlled.controlledAddition_clean_canonical source target sourceCanonical targetCanonical]
  rfl

/-- A multiplier in the addend or saved caller frame is restored after the complete body. -/
lemma operandMultiplier_retained (port : MultiplierPort saved) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (selected : Bool) (retained : Saved) :
    (operandMultiplierBit saved port).get
        (stepList (operandAdditionGates saved)
          ((((source, target), false), (selected, false)), retained)) =
      (operandMultiplierBit saved port).get
        ((((source, target), false), (selected, false)), retained) := by
  rw [operandAddition_clean_canonical saved source target sourceCanonical targetCanonical]
  cases port with
  | addend index =>
      exact (operandSourceBit_get saved index _).trans
        (operandSourceBit_get saved index _).symm
  | retained bit => rfl

/-- The full native realization retains phases for arbitrary external Reference extensions. -/
lemma operandAddition_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved) (operandAdditionProgram saved) environment
      (fun state => (Controlled.controlledAdditionStep state.1, state.2)) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty (operandAdditionGates saved)
    (operandAdditionGates_step saved) environment

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
