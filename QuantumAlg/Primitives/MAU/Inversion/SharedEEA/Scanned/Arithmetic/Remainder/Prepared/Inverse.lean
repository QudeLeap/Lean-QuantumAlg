/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Prepared
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Preservation
import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Inverse

/-!
# Actual inverse of complete paid remainder address and alignment

The actual native adjoint reverses address preparation, both full-word
barrels and arithmetic, returning the original low or signed subtraction.
Every metadata field, original dirty Iter and the entire shared pool
retain their original values. No measurement instrument is inverted.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma focus_add_sub (length : Nat) (signed : Bool)
    (state : Addition.TTK.OverflowRegisters length) :
    ArithmeticWindowProgram.focusStep
        (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow)
        (ArithmeticWindowProgram.focusStep
          (if signed then ArithmeticWindowProgram.Operation.subtractSigned else .subtractLow)
          state) = state := by
  cases signed with
  | false => exact Prod.ext (Addition.TTK.lowOutput_subtractionOutput length state.1) rfl
  | true => exact Addition.TTK.overflowOutput_overflowSubtractionOutput length state

private lemma original_add_sub (width : Nat) (selected : ArithmeticWindowRegisters.Window width)
    (signed : Bool) (state : Registers width) :
    ArithmeticWindowProgram.step selected
        (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow)
        (ArithmeticWindowProgram.step selected
          (if signed then ArithmeticWindowProgram.Operation.subtractSigned else .subtractLow)
          state) = state := by
  simp only [ArithmeticWindowProgram.step, ArithmeticWindowPlacement.placedStep,
    FullPlacement.step, Equiv.apply_symm_apply, focus_add_sub]
  exact (ArithmeticWindowPlacement.placement selected).grouping.symm_apply_apply state

private lemma window_congr (width : Nat) (left right : Registers width)
    (leftAccepted : admitted width left) (rightAccepted : admitted width right)
    (coefficient : left.coefficientLength.toNat = right.coefficientLength.toNat)
    (quotient : left.quotientLength.toNat = right.quotientLength.toNat)
    (shift : left.shift.toNat = right.shift.toNat) :
    window width left leftAccepted = window width right rightAccepted := by
  unfold window
  simp only [coefficient, quotient, shift]

/-- Every original remainder arithmetic mode retains the full positive-window predicate. -/
lemma original_admitted (width : Nat) (selected : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (state : Registers width) :
    admitted width (ArithmeticWindowProgram.step selected operation state) ↔
      admitted width state := by
  have retained := ArithmeticWindowPreservation.remainder_retained selected operation state
  have coefficient := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.1.1.toNat) retained
  have quotient := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.1.2.toNat) retained
  have shift := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.2.toNat) retained
  change (ArithmeticWindowProgram.step selected operation state).coefficientLength.toNat =
    state.coefficientLength.toNat at coefficient
  change (ArithmeticWindowProgram.step selected operation state).quotientLength.toNat =
    state.quotientLength.toNat at quotient
  change (ArithmeticWindowProgram.step selected operation state).shift.toNat = state.shift.toNat
    at shift
  simp only [admitted, coefficient, quotient, shift]

/-- This is the actual entire unitary adjoint, including both paid preparation directions. -/
def inverseProgram (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (program width positive signed).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

/-- Inactive actual inverse execution restores every finite original address and full state. -/
lemma inverseProgram_apply_disabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (inverseProgram width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) :=
  PredicateCompute.dagger_apply_encoded_ket_of_apply (program width positive signed)
    environment state state
    (program_apply_disabled width positive signed environment state clean zero disabled)

/-- Actual inverse execution gives original subtraction and restores the entire same input pool. -/
lemma inverseProgram_apply_enabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : state.1.control = true) (accepted : admitted width state.1) :
    (inverseProgram width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (ArithmeticWindowProgram.step (window width state.1 accepted)
            (if signed then ArithmeticWindowProgram.Operation.subtractSigned else .subtractLow)
            state.1, state.2))) := by
  let selected := window width state.1 accepted
  let operation := if signed then ArithmeticWindowProgram.Operation.subtractSigned else .subtractLow
  let before : Data width := (ArithmeticWindowProgram.step selected operation state.1, state.2)
  have retained := ArithmeticWindowPreservation.remainder_retained selected operation state.1
  have coefficient := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.1.1.toNat) retained
  have quotient := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.1.2.toNat) retained
  have shift := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.2.toNat) retained
  have control := (ArithmeticWindowPreservation.remainder_control selected operation state.1).trans
    enabled
  have beforeAccepted : admitted width before.1 :=
    (original_admitted width selected operation state.1).mpr accepted
  have same := window_congr width before.1 state.1 beforeAccepted accepted
    coefficient quotient shift
  have forward := program_apply_enabled width positive signed environment before
    clean zero addressZero control beforeAccepted
  rw [same] at forward
  have restore := original_add_sub width selected signed state.1
  change ArithmeticWindowProgram.step selected
    (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow) before.1 = state.1
    at restore
  change (program width positive signed).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode before))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode (ArithmeticWindowProgram.step selected
        (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow)
        before.1, state.2))) at forward
  rw [restore] at forward
  exact PredicateCompute.dagger_apply_encoded_ket_of_apply (program width positive signed)
    environment before state forward

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress
