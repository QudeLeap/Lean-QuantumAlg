/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Result
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Disabled
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Program
import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Inverse

/-!
# Actual native coefficient inverse on the complete original window

The arithmetic body is unitary and its actual adjoint realizes the
original low or signed subtraction. No measurement instrument is
inverted, and no specification is extended to an inadmissible address.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow

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
    CoefficientWindowProgram.step selected
        (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow)
        (CoefficientWindowProgram.step selected
          (if signed then ArithmeticWindowProgram.Operation.subtractSigned else .subtractLow)
          state) = state := by
  simp only [CoefficientWindowProgram.step, FullPlacement.step, Equiv.apply_symm_apply,
    focus_add_sub]
  exact (CoefficientWindowProgram.placement selected).grouping.symm_apply_apply state

/-- A disabled actual inverse retains the complete original frame at every finite address. -/
lemma dagger_apply_disabled (width : Nat) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    ((program width signed).dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized
      environment (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) :=
  PredicateCompute.dagger_apply_encoded_ket_of_apply (program width signed) environment state state
    (program_apply_disabled width signed environment state clean zero disabled)

/-- The actual native adjoint computes original subtraction and restores the complete pool. -/
lemma dagger_apply_original_window (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    ((program width signed).dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized
      environment (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (if state.1.control then
          (CoefficientWindowProgram.step
            (CoefficientCoordinates.window width (state.2.1.toNat + 1) (by omega))
            (if signed then ArithmeticWindowProgram.Operation.subtractSigned else .subtractLow)
            state.1, state.2) else state))) := by
  cases enabled : state.1.control with
  | false =>
      simpa only [enabled, Bool.false_eq_true, if_false] using
        dagger_apply_disabled width signed environment state clean zero enabled
  | true =>
      let selected := CoefficientCoordinates.window width (state.2.1.toNat + 1) (by omega)
      let operation := if signed then ArithmeticWindowProgram.Operation.subtractSigned
        else .subtractLow
      let before : Data width := (CoefficientWindowProgram.step selected operation state.1, state.2)
      have control : before.1.control = true :=
        (ArithmeticWindowPreservation.coefficient_control selected operation state.1).trans enabled
      have forward := program_apply_original_window width positive signed environment before
        clean zero within
      rw [control, if_pos rfl] at forward
      have restore := original_add_sub width selected signed state.1
      change CoefficientWindowProgram.step selected
        (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow)
        (CoefficientWindowProgram.step selected operation state.1) = state.1 at restore
      rw [restore] at forward
      have inverse := PredicateCompute.dagger_apply_encoded_ket_of_apply
        (program width signed) environment before state forward
      simpa only [enabled, if_true] using inverse

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow
