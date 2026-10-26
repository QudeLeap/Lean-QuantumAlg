/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Specification
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Pair
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Transform

/-!
# Paid remainder address and two-word alignment with complete native cleanup

One fixed preparation first computes the actual quantum address and
then aligns both original work words by the actual quantum shift.
The actual body returns the preparation of the complete original result;
the same preparation's native adjoint restores the entire physical pool.
Public window coordinates occur only in this proof, never in the program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Actual native preparation depends only on public width and the original quantum operands. -/
def prepareProgram (width : Nat) (positive : 1 ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (ArithmeticAddress.remainderProgram width positive).seq
    (ArithmeticAlignment.pairProgram width .shift)

/-- The same actual preparation acts coherently on every full finite input label. -/
lemma prepareProgram_realizes (width : Nat) (positive : 1 ≤ width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (prepareProgram width positive) environment
      (prepareStep width positive) :=
  (ArithmeticAddress.remainderProgram_realizes width positive environment).seq
    (ArithmeticAlignment.pairProgram_realizes width .shift environment)

/-- Actual address, alignment, body and their reverse execute on the same original full carrier. -/
def program (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  PredicateCompute.program (prepareProgram width positive) (RemainderWindow.program width signed)

/-- Every disabled finite source label restores its full original state and arbitrary address. -/
lemma program_apply_disabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (program width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  let prepared := prepareStep width positive state
  have workspace := prepare_workspace width positive state
  have preparedClean := (congrArg Prod.fst workspace).trans clean
  have preparedZero := (congrArg Prod.snd workspace).trans zero
  have control := (prepare_control width positive state).trans disabled
  have middle := RemainderWindow.program_apply_disabled width signed environment prepared
    preparedClean preparedZero control
  exact PredicateCompute.program_apply_transformed_ket
    (prepareProgram width positive) (RemainderWindow.program width signed)
    (prepareStep width positive) environment (prepareProgram_realizes width positive environment)
    state state middle

/-- Enabled actual arithmetic returns the original full result and restores all shared bits. -/
lemma program_apply_enabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : state.1.control = true) (accepted : admitted width state.1) :
    (program width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (ArithmeticWindowProgram.step (window width state.1 accepted)
            (if signed then .addSigned else .addLow) state.1, state.2))) := by
  let selected := window width state.1 accepted
  let operation := if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow
  let transform := ArithmeticWindowProgram.step selected operation
  let output := ArithmeticAddress.liftSource width transform state
  let addressed := ArithmeticAddress.remainderStep width positive state
  let prepared := prepareStep width positive state
  have workspace := prepare_workspace width positive state
  have preparedClean := (congrArg Prod.fst workspace).trans clean
  have preparedZero := (congrArg Prod.snd workspace).trans zero
  have control := (prepare_control width positive state).trans enabled
  have lengthEq := prepare_length width positive state clean addressZero accepted
  have selectedFits := RemainderCoordinates.fits selected
  have addressFits : prepared.2.1.toNat + 1 ≤ width + 3 := lengthEq.le.trans selectedFits
  have within : prepared.2.1.toNat < width + 3 := by omega
  have middle := RemainderWindow.program_apply width positive signed environment prepared
    preparedClean preparedZero within
  rw [control, if_pos rfl, RemainderWindow.length_congr width
    (prepared.2.1.toNat + 1) selected.length (by omega) selectedFits signed lengthEq] at middle
  have inputMetadata : (ArithmeticGeometry.fieldValue .shift addressed).toNat = selected.below :=
    congrArg (fun value : Registers width => value.shift.toNat)
      (ArithmeticAddress.remainderStep_source width positive state)
  have frameInput : prepared =
      (ArithmeticAlignment.Fixed.frame width selected.below).grouping addressed :=
    ArithmeticAlignment.Fixed.pairGates_eq_frame width selected.below .shift addressed inputMetadata
  have commute := RemainderWindow.address_original_commute width positive selected operation state
  have retained := RemainderWindow.original_field_retained width selected operation .shift state
  have outputMetadata :
      (ArithmeticGeometry.fieldValue .shift
        (ArithmeticAddress.remainderStep width positive output)).toNat = selected.below :=
    (congrArg (fun value : Registers width => value.shift.toNat)
      (ArithmeticAddress.remainderStep_source width positive output)).trans
        (congrArg BitVec.toNat retained)
  have frameOutput := ArithmeticAlignment.Fixed.pairGates_eq_frame width selected.below .shift
    (ArithmeticAddress.remainderStep width positive output) outputMetadata
  have grouped : RemainderWindow.step width selected.length selectedFits signed prepared =
      prepareStep width positive output := by
    rw [frameInput, RemainderWindow.step_aligned]
    change (ArithmeticAlignment.Fixed.frame width selected.below).grouping
      (ArithmeticAddress.liftSource width transform addressed) = _
    rw [← commute]
    exact frameOutput.symm
  have actual := middle.trans (congrArg
    (fun value : Data width => NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode value))) grouped)
  exact PredicateCompute.program_apply_transformed_ket
    (prepareProgram width positive) (RemainderWindow.program width signed)
    (prepareStep width positive) environment (prepareProgram_realizes width positive environment)
    state output actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress
