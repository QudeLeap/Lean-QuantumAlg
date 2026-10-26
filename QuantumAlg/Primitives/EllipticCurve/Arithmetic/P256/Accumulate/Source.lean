/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Doubling
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Controlled.Program
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Swap

/-!
# Actual source doubling beside an arbitrary original accumulator

The original two word roles are interchanged by static physical placement.
No SWAP is executed. The arbitrary accumulator supplies the dirty borrowing
and is restored in full. The complete actual inverse restores the source,
even when the outer multiply-accumulate selector was disabled.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition Horner

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)

/-- Change only the static roles of the two original words, retaining every other wire. -/
def sourcePlacement : FullPlacement (operandEncoding saved) (operandEncoding saved) :=
  (((FullPlacement.prodSwap (BinaryLabelEncoding.finIdentity width)
    (BinaryLabelEncoding.finIdentity width)).appendRight BinaryLabelEncoding.bool).appendRight
      Controlled.flagEncoding).appendRight saved

/-- The semantic view attached to the same actual original physical ports. -/
def swapOperands (state : OperandRegisters Saved) : OperandRegisters Saved :=
  ((((state.1.1.1.2, state.1.1.1.1), state.1.1.2), state.1.2), state.2)

private lemma placement_step (action : OperandRegisters Saved → OperandRegisters Saved)
    (state : OperandRegisters Saved) :
    (sourcePlacement saved).step action state =
      swapOperands (action (swapOperands state)) := rfl

/-- Actual native doubling placed on the original source word. -/
def sourceDoublingProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  (sourcePlacement saved).place (operandDoublingProgram saved)

def sourceDoublingStep (state : OperandRegisters Saved) : OperandRegisters Saved :=
  swapOperands (stepList (operandDoublingGates saved) (swapOperands state))

lemma sourceDoubling_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved) (sourceDoublingProgram saved) environment
      (sourceDoublingStep saved) :=
  UnitaryCircuit.Realizes.congrStep
    ((sourcePlacement saved).place_realizes
      (realizesList (QubitLayout.canonical _) .empty (operandDoublingGates saved) environment))
    (placement_step saved _)

/-- Source doubling restores the entire original arbitrary accumulator and caller frame. -/
lemma sourceDoubling_canonical (source target : Word) (canonical : Canonical source)
    (latch work : Bool) (retained : Saved) :
    sourceDoublingStep saved ((((source, target), false), (latch, work)), retained) =
      ((((Doubling.doubledWord source, target), false), (latch, work)), retained) :=
  congrArg swapOperands
    (operandDoubling_clean_canonical saved target source canonical latch work retained)

/-- Every original forward gate occurs in the complete actual source-restoring inverse. -/
def inverseSourceDoublingProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  (sourcePlacement saved).place (operandInverseDoublingProgram saved)

def inverseSourceDoublingStep (state : OperandRegisters Saved) : OperandRegisters Saved :=
  swapOperands (stepList (operandInverseDoublingGates saved) (swapOperands state))

lemma inverseSourceDoubling_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved) (inverseSourceDoublingProgram saved)
      environment (inverseSourceDoublingStep saved) :=
  ((sourcePlacement saved).place_realizes
    (realizesList (QubitLayout.canonical _) .empty (operandInverseDoublingGates saved)
      environment)).congrStep (placement_step saved _)

/-- Complete actual inverse restoration is valid with any current accumulator word. -/
lemma inverseSourceDoubling_restore (source target : Word) (canonical : Canonical source)
    (latch work : Bool) (retained : Saved) :
    inverseSourceDoublingStep saved
        ((((Doubling.doubledWord source, target), false), (latch, work)), retained) =
      ((((source, target), false), (latch, work)), retained) :=
  congrArg swapOperands
    (operandInverseDoubling_restore saved target source canonical latch work retained)

/-- Static original-wire placement preserves the full forward native ledger. -/
lemma sourceDoubling_eventCost :
    (sourceDoublingProgram saved).eventCost = Doubling.doublingProgram.eventCost :=
  (UnitaryCircuit.placeAt_eventCost _ _ _ _ _).trans (operandDoubling_eventCost saved)

/-- Static original-wire placement preserves the complete native restoration ledger. -/
lemma inverseSourceDoubling_eventCost :
    (inverseSourceDoublingProgram saved).eventCost =
      Doubling.inverseDoublingProgram.eventCost :=
  (UnitaryCircuit.placeAt_eventCost _ _ _ _ _).trans (operandInverseDoubling_eventCost saved)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate
