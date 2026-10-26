/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Controlled.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Operands

/-! # Actual unconditional doubling inside the complete original Horner operand frame -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)

/-- Both latch bits and the complete caller suffix retain their original physical positions. -/
def operandDoublingGates : List (GateSpec (operandEncoding saved)) :=
  (Doubling.doublingGates.map (GateSpec.prodLeft Controlled.flagEncoding)).map
    (GateSpec.prodLeft saved)

def operandDoublingProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (operandDoublingGates saved)

lemma operandDoublingGates_step (state : OperandRegisters Saved) :
    stepList (operandDoublingGates saved) state =
      ((Doubling.doublingStep state.1.1, state.1.2), state.2) := by
  rw [operandDoublingGates, stepList_prodLeft, stepList_prodLeft, Doubling.doublingGates_step]

/-- Every latch and retained caller bit is preserved.
The original arbitrary source supplies borrowing. -/
lemma operandDoubling_clean_canonical (source target : Word) (canonical : Canonical target)
    (latch work : Bool) (retained : Saved) :
    stepList (operandDoublingGates saved)
        ((((source, target), false), (latch, work)), retained) =
      ((((source, Doubling.doubledWord target), false), (latch, work)), retained) :=
  (operandDoublingGates_step saved _).trans
    (congrArg (fun words : Registers => ((words, (latch, work)), retained))
      (Doubling.doubling_clean_canonical source target canonical))

/-- The actual placed gate list retains all phases for every incoming complete frame. -/
lemma operandDoubling_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved) (operandDoublingProgram saved) environment
      (fun state => ((Doubling.doublingStep state.1.1, state.1.2), state.2)) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty (operandDoublingGates saved)
    (operandDoublingGates_step saved) environment

def operandInverseDoublingGates : List (GateSpec (operandEncoding saved)) :=
  (Doubling.inverseDoublingGates.map (GateSpec.prodLeft Controlled.flagEncoding)).map
    (GateSpec.prodLeft saved)

def operandInverseDoublingProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (operandInverseDoublingGates saved)

lemma operandInverseDoubling_restore (source target : Word) (canonical : Canonical target)
    (latch work : Bool) (retained : Saved) :
    stepList (operandInverseDoublingGates saved)
        ((((source, Doubling.doubledWord target), false), (latch, work)), retained) =
      ((((source, target), false), (latch, work)), retained) := by
  rw [operandInverseDoublingGates, stepList_prodLeft, stepList_prodLeft]
  exact congrArg (fun words : Registers => ((words, (latch, work)), retained))
    (Doubling.inverseDoubling_doubledWord source target canonical)

/-- Original caller placement preserves every native event of the complete doubling. -/
lemma operandDoubling_eventCost :
    (operandDoublingProgram saved).eventCost = Doubling.doublingProgram.eventCost := by
  rw [operandDoublingProgram, programList_eventCost, operandDoublingGates,
    map_event_prodLeft, map_event_prodLeft, Doubling.doublingProgram, programList_eventCost]

/-- The complete original inverse pays the same events after placement. -/
lemma operandInverseDoubling_eventCost :
    (operandInverseDoublingProgram saved).eventCost =
      Doubling.inverseDoublingProgram.eventCost := by
  rw [operandInverseDoublingProgram, programList_eventCost, operandInverseDoublingGates,
    map_event_prodLeft, map_event_prodLeft, Doubling.inverseDoublingProgram, programList_eventCost]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
