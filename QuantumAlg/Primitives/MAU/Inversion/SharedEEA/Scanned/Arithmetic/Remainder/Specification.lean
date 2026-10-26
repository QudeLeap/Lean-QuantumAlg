/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Window
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Commutation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Metadata
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Fixed.Runtime

/-! # Original remainder window and complete source preparation -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The complete finite metadata test for a positive original remainder window. -/
def admitted (width : Nat) (state : Registers width) : Prop :=
  state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat < width + 3

/-- Independent original source window, without truncating any metadata operand. -/
def window (width : Nat) (state : Registers width) (accepted : admitted width state) :
    ArithmeticWindowRegisters.Window width where
  above := state.coefficientLength.toNat + state.quotientLength.toNat + 1
  length := width + 3 - (state.coefficientLength.toNat + state.quotientLength.toNat + 1) -
    state.shift.toNat
  below := state.shift.toNat
  complete := by unfold admitted at accepted; omega

/-- Complete actual preparation state, including every original physical pool position. -/
def prepareStep (width : Nat) (positive : 1 ≤ width) (state : Data width) : Data width :=
  GateSpec.stepList (ArithmeticAlignment.pairGates width .shift)
    (ArithmeticAddress.remainderStep width positive state)

private lemma prepare_workspace (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (prepareStep width positive state).2.2 = state.2.2 :=
  (congrArg Prod.snd (ArithmeticAlignment.pairGates_pool width .shift _)).trans
    (ArithmeticAddress.remainderStep_workspace width positive state)

private lemma prepare_control (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (prepareStep width positive state).1.control = state.1.control :=
  (ArithmeticAlignment.pairGates_control width .shift _).trans
    (congrArg (fun value : Registers width => value.control)
      (ArithmeticAddress.remainderStep_source width positive state))

private lemma prepare_length (width : Nat) (positive : 1 ≤ width) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (accepted : admitted width state.1) :
    (prepareStep width positive state).2.1.toNat + 1 =
      (window width state.1 accepted).length := by
  have address := congrArg Prod.fst (ArithmeticAlignment.pairGates_pool width .shift
    (ArithmeticAddress.remainderStep width positive state))
  change (prepareStep width positive state).2.1 =
    (ArithmeticAddress.remainderStep width positive state).2.1 at address
  rw [address, ArithmeticAddress.remainderStep_address_toNat
    width positive state clean zero accepted]
  change width + 3 - 2 - state.1.coefficientLength.toNat - state.1.quotientLength.toNat -
    state.1.shift.toNat + 1 = _
  unfold admitted at accepted
  change _ = width + 3 - (state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1) -
    state.1.shift.toNat
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress
