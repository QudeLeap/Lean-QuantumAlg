/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Commutation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Metadata
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Fixed.Runtime

/-!
# Independent original-window specification for paired remainder arithmetic

The source window uses the complete natural values of the original
metadata. Preparation is a mathematical address transform followed by a
complete wire-permutation equivalence. Neither this specification nor
its final arithmetic result is defined by an executable gate list.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress.Parallel

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- A positive original source window, with no finite-metadata truncation. -/
def admitted (width : Nat) (state : Registers width) : Prop :=
  state.coefficientLength.toNat + state.quotientLength.toNat + 1 + state.shift.toNat < width + 3

/-- Independent coordinates of the original source arithmetic. -/
def window (width : Nat) (state : Registers width) (accepted : admitted width state) :
    ArithmeticWindowRegisters.Window width where
  above := state.coefficientLength.toNat + state.quotientLength.toNat + 1
  length := width + 3 - (state.coefficientLength.toNat + state.quotientLength.toNat + 1) -
    state.shift.toNat
  below := state.shift.toNat
  complete := by unfold admitted at accepted; omega

/-- Complete mathematical preparation includes every original source and pool position. -/
def prepareStep (width : Nat) (positive : 1 ≤ width) (state : Data width) : Data width :=
  (ArithmeticAlignment.Fixed.frame width state.1.shift.toNat).grouping
    (ArithmeticAddress.remainderStep width positive state)

private lemma prepareStep_eq_sourceGates (width : Nat) (positive : 1 ≤ width)
    (state : Data width) :
    prepareStep width positive state =
      GateSpec.stepList (ArithmeticAlignment.pairGates width .shift)
        (ArithmeticAddress.remainderStep width positive state) := by
  symm
  apply ArithmeticAlignment.Fixed.pairGates_eq_frame
  exact congrArg (fun value : Registers width => value.shift.toNat)
    (ArithmeticAddress.remainderStep_source width positive state)

private lemma prepare_workspace (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (prepareStep width positive state).2.2 = state.2.2 := by
  rw [prepareStep_eq_sourceGates]
  exact (congrArg Prod.snd (ArithmeticAlignment.pairGates_pool width .shift _)).trans
    (ArithmeticAddress.remainderStep_workspace width positive state)

private lemma prepare_control (width : Nat) (positive : 1 ≤ width) (state : Data width) :
    (prepareStep width positive state).1.control = state.1.control := by
  rw [prepareStep_eq_sourceGates]
  exact (ArithmeticAlignment.pairGates_control width .shift _).trans
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
  rw [← prepareStep_eq_sourceGates] at address
  rw [address, ArithmeticAddress.remainderStep_address_toNat
    width positive state clean zero accepted]
  change width + 3 - 2 - state.1.coefficientLength.toNat - state.1.quotientLength.toNat -
    state.1.shift.toNat + 1 = _
  unfold admitted at accepted
  change _ = width + 3 - (state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1) -
    state.1.shift.toNat
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress.Parallel
