/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Controlled.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Operands

/-! # Exact readouts and physical separation of original Horner control ports -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)

/-- Proof-side value of the original multiplier port; the actual program still uses its wire. -/
def operandMultiplierValue (port : MultiplierPort saved) (source : Word) (retained : Saved) :
    Bool :=
  match port with
  | .addend index => source.val.testBit index.val
  | .retained bit => bit.get retained

lemma operandMultiplierBit_get (port : MultiplierPort saved) (state : OperandRegisters Saved) :
    (operandMultiplierBit saved port).get state =
      operandMultiplierValue saved port state.1.1.1.1 state.2 := by
  cases port with
  | addend index => exact operandSourceBit_get saved index state
  | retained bit => rfl

lemma operandSavedBit_get (bit : EncodedBit saved) (state : OperandRegisters Saved) :
    (operandSavedBit saved bit).get state = bit.get state.2 := rfl

/-- Only the original selected-add latch changes, with the complete caller frame retained. -/
lemma operandLatchBit_flip (state : OperandRegisters Saved) :
    (operandLatchBit saved).flip state =
      ((state.1.1, (!state.1.2.1, state.1.2.2)), state.2) := rfl

private lemma source_wire_value (index : Fin width) :
    (operandSourceBit saved index).wire.val = width - 1 - index.val := rfl

private lemma latch_wire_value : (operandLatchBit saved).wire.val = 513 := rfl

private lemma saved_wire_value (bit : EncodedBit saved) :
    (operandSavedBit saved bit).wire.val = 515 + bit.wire.val := rfl

/-- A retained outer selector never aliases the original clean arithmetic latch. -/
lemma operandSaved_latch_ne (bit : EncodedBit saved) :
    (operandSavedBit saved bit).wire ≠ (operandLatchBit saved).wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [saved_wire_value, latch_wire_value] at positions
  omega

/-- Both allowed multiplier locations are physically distinct from the original latch. -/
lemma operandMultiplier_latch_ne (port : MultiplierPort saved) :
    (operandMultiplierBit saved port).wire ≠ (operandLatchBit saved).wire := by
  cases port with
  | addend index =>
      intro same
      have positions := congrArg Fin.val same
      change (operandSourceBit saved index).wire.val =
        (operandLatchBit saved).wire.val at positions
      rw [source_wire_value, latch_wire_value] at positions
      have bounded := index.isLt
      change index.val < 256 at bounded
      change 256 - 1 - index.val = 513 at positions
      omega
  | retained bit => exact operandSaved_latch_ne saved bit

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
