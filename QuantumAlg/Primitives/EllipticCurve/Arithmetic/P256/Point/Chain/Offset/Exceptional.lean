/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Predicate.Negative
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Program

/-!
# Actual exceptional quantum table-word addition

The loaded table word already contains the negative exceptional slope.
The real E and N systems select E and not N on the existing arithmetic
latch. Four physical X gates and two physical Toffolis bracket the same
native quantum-operand addition. Both controls and every caller system
are retained; no quantum value is converted into a host-selected constant.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset

namespace Exceptional

noncomputable section

open EncodedBit GateSpec Horner

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)

private lemma saved_ne (enable normal : EncodedBit saved)
    (distinct : enable.wire ≠ normal.wire) :
    (operandSavedBit saved enable).wire ≠ (operandSavedBit saved normal).wire := by
  intro same
  apply distinct
  apply Fin.ext
  have positions := congrArg Fin.val same
  change 515 + enable.wire.val = 515 + normal.wire.val at positions
  omega

private def guard (enable normal : EncodedBit saved) (distinct : enable.wire ≠ normal.wire) :
    List (GateSpec (operandEncoding saved)) :=
  negativeConjunction (operandSavedBit saved enable) (operandSavedBit saved normal)
    (operandLatchBit saved) (saved_ne saved enable normal distinct)
    (operandSaved_latch_ne saved enable) (operandSaved_latch_ne saved normal)

private lemma guard_step (enable normal : EncodedBit saved)
    (distinct : enable.wire ≠ normal.wire) (source target : Word)
    (reduction latch work : Bool) (retained : Saved) :
    stepList (guard saved enable normal distinct)
        ((((source, target), reduction), (latch, work)), retained) =
      ((((source, target), reduction),
        (latch ^^ (enable.get retained && Bool.not (normal.get retained)), work)), retained) := by
  rw [guard, negativeConjunction_step]
  change (if enable.get retained && Bool.not (normal.get retained) then
    (operandLatchBit saved).flip ((((source, target), reduction), (latch, work)), retained)
    else ((((source, target), reduction), (latch, work)), retained)) = _
  rw [operandLatchBit_flip]
  cases enable.get retained <;> cases normal.get retained <;> cases latch <;> rfl

/-- The actual E and negative N guards use the original clean selector latch. -/
def gates (enable normal : EncodedBit saved) (distinct : enable.wire ≠ normal.wire) :
    List (GateSpec (operandEncoding saved)) :=
  guard saved enable normal distinct ++ operandAdditionGates saved ++
    guard saved enable normal distinct

/-- Same existing bank and source word, with two retained physical quantum controls. -/
def program (enable normal : EncodedBit saved) (distinct : enable.wire ≠ normal.wire) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates saved enable normal distinct)

private lemma sandwich_step {Data : Type} {encoding : BinaryLabelEncoding Data}
    (before body : List (GateSpec encoding)) (state : Data) :
    stepList (before ++ body ++ before) state =
      stepList before (stepList body (stepList before state)) := by
  rw [stepList_append, stepList_append]

/-- Unrestricted full raw basis action of the real instructions. -/
lemma program_realizes (enable normal : EncodedBit saved)
    (distinct : enable.wire ≠ normal.wire) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (operandEncoding saved) (program saved enable normal distinct)
      environment (stepList (gates saved enable normal distinct)) :=
  realizesList (QubitLayout.canonical _) .empty _ environment

/-- Canonical residues are required only on E and not N; all other operands remain arbitrary. -/
lemma gates_admitted (enable normal : EncodedBit saved) (distinct : enable.wire ≠ normal.wire)
    (source target : Word) (retained : Saved)
    (sourceCanonical : (enable.get retained && Bool.not (normal.get retained)) = true →
      Canonical source)
    (targetCanonical : (enable.get retained && Bool.not (normal.get retained)) = true →
      Canonical target) :
    stepList (gates saved enable normal distinct)
        ((((source, target), false), (false, false)), retained) =
      ((((source, if enable.get retained && Bool.not (normal.get retained) then
        ModularAddition.modularSumWord source target else target), false),
        (false, false)), retained) := by
  let selected := enable.get retained && Bool.not (normal.get retained)
  let output := if selected then ModularAddition.modularSumWord source target else target
  let before : OperandRegisters Saved :=
    ((((source, target), false), (selected, false)), retained)
  let after : OperandRegisters Saved :=
    ((((source, output), false), (selected, false)), retained)
  have first : stepList (guard saved enable normal distinct)
      ((((source, target), false), (false, false)), retained) = before :=
    (guard_step saved enable normal distinct source target false false false retained).trans
      (congrArg (fun bit : Bool => ((((source, target), false), (bit, false)), retained))
        (Bool.false_xor selected))
  have body : stepList (operandAdditionGates saved) before = after :=
    Offset.addition_admitted saved source target selected retained sourceCanonical targetCanonical
  have last : stepList (guard saved enable normal distinct) after =
      ((((source, output), false), (false, false)), retained) :=
    (guard_step saved enable normal distinct source output false selected false retained).trans
      (congrArg (fun bit : Bool => ((((source, output), false), (bit, false)), retained))
        (Bool.xor_self selected))
  exact (sandwich_step _ _ _).trans
    ((congrArg (stepList (guard saved enable normal distinct))
      ((congrArg (stepList (operandAdditionGates saved)) first).trans body)).trans last)

end

end Exceptional

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset
