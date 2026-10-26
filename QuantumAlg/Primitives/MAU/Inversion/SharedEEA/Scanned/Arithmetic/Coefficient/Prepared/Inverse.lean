/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Prepared
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Inverse

/-!
# Actual inverse of the paid complete coefficient-address sandwich

The unitary adjoint reverses actual native instructions, including both
address preparations. Its exact original subtraction action retains the
complete source geometry and restores the same whole input pool. No
measurement instrument or external source computation is inverted.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Every original coefficient arithmetic mode retains the complete natural address geometry. -/
lemma original_geometry (width : Nat) (selected : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (state : Registers width) :
    wordLength width (CoefficientWindowProgram.step selected operation state) =
        wordLength width state ∧
      (admitted width (CoefficientWindowProgram.step selected operation state) ↔
        admitted width state) := by
  have retained := ArithmeticWindowPreservation.coefficient_retained selected operation state
  have coefficient := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.1.1) retained
  have divisor := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.1) retained
  have shift := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.2) retained
  have second := congrArg
    (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.2) retained
  change (CoefficientWindowProgram.step selected operation state).coefficientLength =
    state.coefficientLength at coefficient
  change (CoefficientWindowProgram.step selected operation state).divisorLength =
    state.divisorLength at divisor
  change (CoefficientWindowProgram.step selected operation state).shift = state.shift at shift
  change (CoefficientWindowProgram.step selected operation state).flags.second =
    state.flags.second at second
  simp only [wordLength, admitted, coefficient, divisor, shift, second, and_self, iff_self]

/-- The actual whole native adjoint includes the paid address compute and cleanup instructions. -/
def inverseProgram (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (program width positive signed).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

/-- The complete actual adjoint is inactive on every finite address under disabled source Ctrl. -/
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

/-- Original subtraction restores all address/prefix/conjunction bits through the actual adjoint. -/
lemma inverseProgram_apply_enabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : state.1.control = true) (accepted : admitted width state.1) :
    (inverseProgram width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (CoefficientWindowProgram.step
            (CoefficientCoordinates.window width (wordLength width state.1)
              (wordLength_fits width state.1 accepted))
            (if signed then ArithmeticWindowProgram.Operation.subtractSigned else .subtractLow)
            state.1, state.2))) := by
  let selected := CoefficientCoordinates.window width (wordLength width state.1)
    (wordLength_fits width state.1 accepted)
  let operation := if signed then ArithmeticWindowProgram.Operation.subtractSigned
    else .subtractLow
  let before : Data width := (CoefficientWindowProgram.step selected operation state.1, state.2)
  have geometry := original_geometry width selected operation state.1
  have control : before.1.control = true :=
    (ArithmeticWindowPreservation.coefficient_control selected operation state.1).trans enabled
  have beforeAccepted : admitted width before.1 := geometry.2.mpr accepted
  have forward := program_apply_enabled width positive signed environment before
    clean zero addressZero control beforeAccepted
  have restore := CoefficientWindow.original_add_sub width selected signed state.1
  change CoefficientWindowProgram.step selected
    (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow)
    before.1 = state.1 at restore
  have selectedSame := window_congr width (wordLength width before.1)
    (wordLength width state.1) geometry.1
    (wordLength_fits width before.1 beforeAccepted) (wordLength_fits width state.1 accepted)
  rw [selectedSame] at forward
  change (program width positive signed).applyNormalized environment
    (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode before))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode
        (CoefficientWindowProgram.step selected
          (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow)
          before.1, state.2))) at forward
  rw [restore] at forward
  exact PredicateCompute.dagger_apply_encoded_ket_of_apply (program width positive signed)
    environment before state forward

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientAddress
