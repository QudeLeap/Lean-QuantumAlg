/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Controlled.Resources

/-!
# Actual selected addition of an already loaded quantum table word

The source word contains the value from the actual quantum-addressed
lookup. Two real CNOTs copy and clear a retained selector on the original
clean addition latch. The intervening program is the same proved native
two-quantum-operand modular addition. No host value selects an addend.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset

noncomputable section

open EncodedBit GateSpec Horner

private lemma bracket_step {Data : Type} {encoding : BinaryLabelEncoding Data}
    (guard : GateSpec encoding) (body : List (GateSpec encoding)) (state : Data) :
    stepList ([guard] ++ body ++ [guard]) state =
      guard.step (stepList body (guard.step state)) := by
  rw [stepList_append, stepList_append]
  rfl

private lemma bracket_map {First Second : Type} (action : First → Second)
    (guard : First) (body : List First) :
    ([guard] ++ body ++ [guard]).map action =
      [action guard] ++ body.map action ++ [action guard] := by
  rw [List.map_append, List.map_append]
  rfl

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)

private def selectorCopy (selector : EncodedBit saved) : GateSpec (operandEncoding saved) :=
  .cnot (operandSavedBit saved selector) (operandLatchBit saved)
    (operandSaved_latch_ne saved selector)

private lemma selectorCopy_step (selector : EncodedBit saved)
    (source target : Word) (reduction latch work : Bool) (retained : Saved) :
    (selectorCopy saved selector).step
        ((((source, target), reduction), (latch, work)), retained) =
      ((((source, target), reduction), (latch ^^ selector.get retained, work)), retained) := by
  change cnotStep (operandSavedBit saved selector) (operandLatchBit saved) _ = _
  rw [cnotStep, operandSavedBit_get]
  cases selected : selector.get retained
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
    rfl
  · simp only [↓reduceIte, operandLatchBit_flip, Bool.xor_true]
    rfl

/-- The exact original native modular addition is bracketed by two paid selector copies. -/
def gates (selector : EncodedBit saved) : List (GateSpec (operandEncoding saved)) :=
  [selectorCopy saved selector] ++ operandAdditionGates saved ++ [selectorCopy saved selector]

/-- The loaded source and retained selector are real quantum systems on the same existing bank. -/
def program (selector : EncodedBit saved) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates saved selector)

private lemma gates_step (selector : EncodedBit saved) (state : OperandRegisters Saved) :
    stepList (gates saved selector) state =
      (selectorCopy saved selector).step (stepList (operandAdditionGates saved)
        ((selectorCopy saved selector).step state)) :=
  bracket_step _ _ _

/-- Complete raw semantics, without imposing any canonical input premise. -/
lemma program_realizes (selector : EncodedBit saved)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved) (program saved selector) environment
      (stepList (gates saved selector)) :=
  realizesList (QubitLayout.canonical _) .empty _ environment

private lemma addition_admitted (source target : Word) (selected : Bool) (retained : Saved)
    (sourceCanonical : selected = true → Canonical source)
    (targetCanonical : selected = true → Canonical target) :
    stepList (operandAdditionGates saved)
        ((((source, target), false), (selected, false)), retained) =
      ((((source, if selected then ModularAddition.modularSumWord source target else target),
        false), (selected, false)), retained) := by
  cases selected with
  | false =>
      exact (operandAdditionGates_step saved _).trans
        (congrArg (fun frame => (frame, retained))
          (ModularAddition.Controlled.controlledAddition_of_selector_false _ rfl))
  | true =>
      exact operandAddition_clean_canonical saved source target (sourceCanonical rfl)
        (targetCanonical rfl) true retained

/-- Only active canonical sectors need residue premises; the loaded word and every flag return. -/
lemma gates_admitted (selector : EncodedBit saved) (source target : Word) (retained : Saved)
    (sourceCanonical : selector.get retained = true → Canonical source)
    (targetCanonical : selector.get retained = true → Canonical target) :
    stepList (gates saved selector) ((((source, target), false), (false, false)), retained) =
      ((((source, if selector.get retained then ModularAddition.modularSumWord source target
        else target), false), (false, false)), retained) := by
  let selected := selector.get retained
  let output := if selected then ModularAddition.modularSumWord source target else target
  let before : OperandRegisters Saved :=
    ((((source, target), false), (selected, false)), retained)
  let after : OperandRegisters Saved :=
    ((((source, output), false), (selected, false)), retained)
  have first : (selectorCopy saved selector).step
      ((((source, target), false), (false, false)), retained) = before :=
    (selectorCopy_step saved selector source target false false false retained).trans
      (congrArg (fun bit : Bool => ((((source, target), false), (bit, false)), retained))
        (Bool.false_xor selected))
  have body : stepList (operandAdditionGates saved) before = after :=
    addition_admitted saved source target selected retained sourceCanonical targetCanonical
  have last : (selectorCopy saved selector).step after =
      ((((source, output), false), (false, false)), retained) :=
    (selectorCopy_step saved selector source output false selected false retained).trans
      (congrArg (fun bit : Bool => ((((source, output), false), (bit, false)), retained))
        (Bool.xor_self selected))
  exact (gates_step saved selector _).trans
    ((congrArg (selectorCopy saved selector).step
      ((congrArg (stepList (operandAdditionGates saved)) first).trans body)).trans last)

/-- The inactive selector admits arbitrary binary operands and retains all complete caller data. -/
lemma gates_inactive (selector : EncodedBit saved) (source target : Word) (retained : Saved)
    (inactive : selector.get retained = false) :
    stepList (gates saved selector) ((((source, target), false), (false, false)), retained) =
      ((((source, target), false), (false, false)), retained) := by
  have impossible : selector.get retained = true → False := by simp only [inactive]; decide
  simpa only [inactive, Bool.false_eq_true, ↓reduceIte] using
    gates_admitted saved selector source target retained
      (fun active => (impossible active).elim) (fun active => (impossible active).elim)

/-- Every realized native occurrence remains in the actual sequential event word. -/
lemma program_eventTrace (selector : EncodedBit saved) :
    (program saved selector).eventTrace =
      [.gate .cnot] ++ (operandAdditionProgram saved).eventTrace ++ [.gate .cnot] := by
  have original := programList_eventTrace (QubitLayout.canonical (operandEncoding saved).width)
    .empty (gates saved selector)
  have middle := programList_eventTrace (QubitLayout.canonical (operandEncoding saved).width)
    .empty (operandAdditionGates saved)
  exact original.trans ((bracket_map (event .empty) (selectorCopy saved selector)
    (operandAdditionGates saved)).trans
      (congrArg (fun events => [.gate .cnot] ++ events ++ [.gate .cnot]) middle.symm))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset
