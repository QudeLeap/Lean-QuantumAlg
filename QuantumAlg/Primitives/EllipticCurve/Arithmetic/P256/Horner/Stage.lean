/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Operands
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Selection

/-!
# One actual multiplier-bit selection and complete modular-addition stage

The physical multiplier bit is latched before borrowing. The complete native
selected-add body restores it before the same actual Toffoli clears the
original latch. Both allowed original multiplier locations are covered.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (port : MultiplierPort saved) (outer : EncodedBit saved)
  (outerMultiplier : (operandSavedBit saved outer).wire ≠
    (operandMultiplierBit saved port).wire)

/-- The physical stage uses only the original native arithmetic and original caller wires. -/
def stageGates : List (GateSpec (operandEncoding saved)) :=
  Selection.gates (operandSavedBit saved outer) (operandMultiplierBit saved port)
    (operandLatchBit saved) outerMultiplier (operandSaved_latch_ne saved outer)
    (operandMultiplier_latch_ne saved port) (operandAdditionGates saved)

def stageProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  Selection.program (operandSavedBit saved outer) (operandMultiplierBit saved port)
    (operandLatchBit saved) outerMultiplier (operandSaved_latch_ne saved outer)
    (operandMultiplier_latch_ne saved port) (operandAdditionGates saved)

private lemma latch_step (source target : Word) (reduction latch work : Bool) (retained : Saved) :
    toffoliStep (operandSavedBit saved outer) (operandMultiplierBit saved port)
        (operandLatchBit saved) ((((source, target), reduction), (latch, work)), retained) =
      ((((source, target), reduction),
        (latch ^^ (outer.get retained && operandMultiplierValue saved port source retained), work)),
        retained) := by
  rw [toffoliStep, operandSavedBit_get, operandMultiplierBit_get]
  change (if outer.get retained && operandMultiplierValue saved port source retained then
      (operandLatchBit saved).flip ((((source, target), reduction), (latch, work)), retained)
    else ((((source, target), reduction), (latch, work)), retained)) = _
  cases selected : outer.get retained && operandMultiplierValue saved port source retained
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
    rfl
  · simp only [↓reduceIte, operandLatchBit_flip, Bool.xor_true]
    rfl

/-- Exact full-label branch output retains the source, saved multiplier
and both original clean bits. -/
lemma stage_clean_canonical (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Saved) :
    stepList (stageGates saved port outer outerMultiplier)
        ((((source, target), false), (false, false)), retained) =
      ((((source, if outer.get retained && operandMultiplierValue saved port source retained then
          modularSumWord source target else target), false), (false, false)), retained) := by
  let selected := outer.get retained && operandMultiplierValue saved port source retained
  let result := if selected then modularSumWord source target else target
  let latch := toffoliStep (operandSavedBit saved outer) (operandMultiplierBit saved port)
    (operandLatchBit saved)
  have computed : latch ((((source, target), false), (false, false)), retained) =
      ((((source, target), false), (selected, false)), retained) :=
    (latch_step saved port outer source target false false false retained).trans
      (congrArg (fun bit : Bool => ((((source, target), false), (bit, false)), retained))
        (Bool.false_xor selected))
  have body := operandAddition_clean_canonical saved source target sourceCanonical
    targetCanonical selected retained
  have cleared : latch ((((source, result), false), (selected, false)), retained) =
      ((((source, result), false), (false, false)), retained) :=
    (latch_step saved port outer source result false selected false retained).trans
      (congrArg (fun bit : Bool => ((((source, result), false), (bit, false)), retained))
        (Bool.xor_self selected))
  have actual := Selection.gates_step (operandSavedBit saved outer)
    (operandMultiplierBit saved port) (operandLatchBit saved) outerMultiplier
    (operandSaved_latch_ne saved outer) (operandMultiplier_latch_ne saved port)
    (operandAdditionGates saved) ((((source, target), false), (false, false)), retained)
  have afterBody := (congrArg (stepList (operandAdditionGates saved)) computed).trans body
  exact actual.trans ((congrArg latch afterBody).trans cleared)

/-- Literal native execution has its full-frame action on every incoming quantum label. -/
lemma stage_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved)
      (stageProgram saved port outer outerMultiplier) environment
      (stepList (stageGates saved port outer outerMultiplier)) :=
  Selection.realizes (operandSavedBit saved outer) (operandMultiplierBit saved port)
    (operandLatchBit saved) outerMultiplier (operandSaved_latch_ne saved outer)
    (operandMultiplier_latch_ne saved port) (operandAdditionGates saved) environment

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
