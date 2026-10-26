/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Multiplier
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Source
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Program
import all QuantumAlg.Components.Encoded.BitGates.IterationLaws

/-!
# Actual quantum multiply-accumulate with complete source restoration

The fixed low-to-high schedule pays 256 bit-latched selected additions,
255 unconditional source doublings and all 255 actual inverse doublings.
The accumulator need not be zero. The separate original multiplier word
is read before borrowing and restored by each complete selected-add stage.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

noncomputable section

open QuantumAlg.EncodedBit GateSpec Horner

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : RetainedMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (.retained (multiplier.bits index))).wire)

def forwardRoundProgram (index : Fin width) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  if index.val = 0 then stageProgram saved (.retained (multiplier.bits index)) outer
    (outerMultiplier index)
  else UnitaryCircuit.seq (sourceDoublingProgram saved)
    (stageProgram saved (.retained (multiplier.bits index)) outer (outerMultiplier index))

def forwardRoundStep (index : Fin width) (state : OperandRegisters Saved) :
    OperandRegisters Saved :=
  if index.val = 0 then stepList (stageGates saved (.retained (multiplier.bits index)) outer
    (outerMultiplier index)) state
  else stepList (stageGates saved (.retained (multiplier.bits index)) outer
    (outerMultiplier index)) (sourceDoublingStep saved state)

lemma forwardRound_realizes (index : Fin width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved)
      (forwardRoundProgram saved multiplier outer outerMultiplier index) environment
      (forwardRoundStep saved multiplier outer outerMultiplier index) :=
  Horner.round_realizes (operandEncoding saved) (QubitLayout.canonical _) environment
    (index.val = 0) (sourceDoublingProgram saved)
    (stageProgram saved (.retained (multiplier.bits index)) outer (outerMultiplier index))
    (sourceDoublingStep saved)
    (stepList (stageGates saved (.retained (multiplier.bits index)) outer
      (outerMultiplier index)))
    (sourceDoubling_realizes saved environment) (stage_realizes saved _ outer _ environment)

def forwardProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  (List.ofFn (forwardRoundProgram saved multiplier outer outerMultiplier)).foldr
    UnitaryCircuit.seq (UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical (operandEncoding saved).width).toQuantum)

def forwardStep : OperandRegisters Saved → OperandRegisters Saved :=
  UnitaryCircuit.Realizes.stepList
    (List.ofFn (forwardRoundStep saved multiplier outer outerMultiplier))

lemma forward_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved)
      (forwardProgram saved multiplier outer outerMultiplier) environment
      (forwardStep saved multiplier outer outerMultiplier) :=
  Horner.realizes_ofFn (operandEncoding saved) (QubitLayout.canonical _) environment
    (forwardRoundProgram saved multiplier outer outerMultiplier)
    (forwardRoundStep saved multiplier outer outerMultiplier)
    (fun index => forwardRound_realizes saved multiplier outer outerMultiplier index environment)

/-- All original source doublings are undone by the complete actual inverse program. -/
def restorationProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  UnitaryCircuit.iterate (width - 1) (inverseSourceDoublingProgram saved)

def program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  UnitaryCircuit.seq (forwardProgram saved multiplier outer outerMultiplier)
    (restorationProgram saved)

def fullStep (state : OperandRegisters Saved) : OperandRegisters Saved :=
  (inverseSourceDoublingStep saved)^[width - 1]
    (forwardStep saved multiplier outer outerMultiplier state)

private lemma restored_realizes {Data : Type} (encoding : BinaryLabelEncoding Data)
    (layout : QubitLayout encoding.width) (environment : OracleModel.empty.Interpretation)
    (first inverse : UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum)
    (firstStep inverseStep : Data → Data) (count : Nat)
    (firstLaw : UnitaryCircuit.Realizes encoding first environment firstStep)
    (inverseLaw : UnitaryCircuit.Realizes encoding inverse environment inverseStep) :
    UnitaryCircuit.Realizes encoding
      (UnitaryCircuit.seq first (UnitaryCircuit.iterate count inverse)) environment
      (fun state => inverseStep^[count] (firstStep state)) :=
  UnitaryCircuit.Realizes.seq (firstStep := firstStep) (secondStep := inverseStep^[count])
    firstLaw (inverseLaw.iterate count)

/-- Full phase-exact native semantics includes complete inverse source restoration. -/
lemma realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved)
      (program saved multiplier outer outerMultiplier) environment
      (fullStep saved multiplier outer outerMultiplier) :=
  restored_realizes (operandEncoding saved) (QubitLayout.canonical _) environment
    (forwardProgram saved multiplier outer outerMultiplier) (inverseSourceDoublingProgram saved)
    (forwardStep saved multiplier outer outerMultiplier) (inverseSourceDoublingStep saved)
    (width - 1) (forward_realizes saved multiplier outer outerMultiplier environment)
    (inverseSourceDoubling_realizes saved environment)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate
