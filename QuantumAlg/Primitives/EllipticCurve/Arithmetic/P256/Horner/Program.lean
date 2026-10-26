/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Multiplier
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Stage
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Doubling
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.OfFn

/-!
# Actual high-to-low quantum-operand Horner program

The fixed schedule contains 256 paid multiplier-bit selections and 255
actual unconditional target doublings. The first target doubling is omitted
because the target is initially zero. Both source operands remain quantum;
only public bit indices determine program syntax.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : QuantumMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (multiplier.ports index)).wire)

/-- Public MSB-to-LSB address; no runtime quantum value selects a circuit. -/
def highIndex (index : Fin width) : Fin width := index.rev

/-- A literal first selection, followed by literal double-and-select stages. -/
def cleanRoundProgram (index : Fin width) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  if index.val = 0 then stageProgram saved (multiplier.ports (highIndex index)) outer
    (outerMultiplier (highIndex index))
  else UnitaryCircuit.seq (operandDoublingProgram saved)
    (stageProgram saved (multiplier.ports (highIndex index)) outer
      (outerMultiplier (highIndex index)))

/-- The full raw label update of the same actual round. -/
def cleanRoundStep (index : Fin width) (state : OperandRegisters Saved) :
    OperandRegisters Saved :=
  if index.val = 0 then stepList (stageGates saved (multiplier.ports (highIndex index)) outer
    (outerMultiplier (highIndex index))) state
  else stepList (stageGates saved (multiplier.ports (highIndex index)) outer
    (outerMultiplier (highIndex index))) (stepList (operandDoublingGates saved) state)

private lemma round_realizes {Data : Type} (encoding : BinaryLabelEncoding Data)
    (layout : QubitLayout encoding.width) (environment : OracleModel.empty.Interpretation)
    (first : Prop) [Decidable first]
    (doubling addition : UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum)
    (doubleStep addStep : Data → Data)
    (doubleLaw : UnitaryCircuit.Realizes encoding doubling environment doubleStep)
    (addLaw : UnitaryCircuit.Realizes encoding addition environment addStep) :
    UnitaryCircuit.Realizes encoding
      (if first then addition else UnitaryCircuit.seq doubling addition) environment
      (fun state => if first then addStep state else addStep (doubleStep state)) := by
  by_cases selected : first
  · simpa only [selected, ↓reduceIte] using addLaw
  · simpa only [selected, ↓reduceIte] using UnitaryCircuit.Realizes.seq doubleLaw addLaw

lemma cleanRound_realizes (index : Fin width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved)
      (cleanRoundProgram saved multiplier outer outerMultiplier index) environment
      (cleanRoundStep saved multiplier outer outerMultiplier index) :=
  round_realizes (operandEncoding saved) (QubitLayout.canonical _) environment (index.val = 0)
    (operandDoublingProgram saved)
    (stageProgram saved (multiplier.ports (highIndex index)) outer
      (outerMultiplier (highIndex index)))
    (stepList (operandDoublingGates saved))
    (stepList (stageGates saved (multiplier.ports (highIndex index)) outer
      (outerMultiplier (highIndex index))))
    (realizesList (QubitLayout.canonical _) .empty (operandDoublingGates saved) environment)
    (stage_realizes saved _ outer _ environment)

/-- Original native instruction trees in their actual high-to-low execution order. -/
def cleanProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  (List.ofFn (cleanRoundProgram saved multiplier outer outerMultiplier)).foldr
    UnitaryCircuit.seq (UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical (operandEncoding saved).width).toQuantum)

/-- Full raw semantics of every actual stage, including all original work and caller wires. -/
def cleanStep : OperandRegisters Saved → OperandRegisters Saved :=
  UnitaryCircuit.Realizes.stepList
    (List.ofFn (cleanRoundStep saved multiplier outer outerMultiplier))

private lemma realizes_ofFn {Data : Type} (encoding : BinaryLabelEncoding Data)
    (layout : QubitLayout encoding.width) (environment : OracleModel.empty.Interpretation)
    {count : Nat} (programs : Fin count →
      UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum)
    (steps : Fin count → Data → Data)
    (laws : ∀ index, UnitaryCircuit.Realizes encoding (programs index) environment
      (steps index)) :
    UnitaryCircuit.Realizes encoding
      ((List.ofFn programs).foldr UnitaryCircuit.seq
        (UnitaryCircuit.identity AlgorithmGate.model .empty layout.toQuantum)) environment
      (UnitaryCircuit.Realizes.stepList (List.ofFn steps)) := by
  apply UnitaryCircuit.Realizes.appendList
  apply List.forall₂_of_length_eq_of_get
  · simp only [List.length_ofFn]
  · intro index leftBound rightBound
    simp only [List.get_ofFn]
    exact laws _

/-- The complete native Horner tree retains phase for every full input quantum label. -/
lemma clean_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved)
      (cleanProgram saved multiplier outer outerMultiplier) environment
      (cleanStep saved multiplier outer outerMultiplier) :=
  realizes_ofFn (operandEncoding saved) (QubitLayout.canonical _) environment
    (cleanRoundProgram saved multiplier outer outerMultiplier)
    (cleanRoundStep saved multiplier outer outerMultiplier)
    (fun index => cleanRound_realizes saved multiplier outer outerMultiplier index environment)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
