/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Result
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Disabled
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Commutation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Coefficient.Natural
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Coefficient.Runtime
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Transform

/-!
# Paid coefficient address, actual arithmetic and complete native cleanup

The same fixed program computes the original phase-dependent address,
executes the actual coefficient traversal, and runs the actual preparation
adjoint. The enabled theorem requires the complete natural window range;
the disabled theorem covers every finite address without a range premise.
The original source-phase guard is a separate actual circuit.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Complete original finite metadata admits a positive coefficient arithmetic window. -/
def admitted (width : Nat) (state : Registers width) : Prop :=
  if state.flags.second then state.divisorLength.toNat + state.shift.toNat < width + 3
  else state.coefficientLength.toNat + 1 ≤ width + 3

/-- Independent source length, retaining full finite metadata and natural subtraction. -/
def wordLength (width : Nat) (state : Registers width) : Nat :=
  if state.flags.second then width + 3 - state.divisorLength.toNat - state.shift.toNat
  else state.coefficientLength.toNat + 1

lemma wordLength_positive (width : Nat) (state : Registers width)
    (accepted : admitted width state) : 0 < wordLength width state := by
  unfold admitted at accepted
  unfold wordLength
  split_ifs at accepted ⊢ <;> omega

lemma wordLength_fits (width : Nat) (state : Registers width)
    (accepted : admitted width state) : wordLength width state ≤ width + 3 := by
  unfold admitted at accepted
  unfold wordLength
  split_ifs at accepted ⊢ <;> omega

/-- The actual original-phase native address encodes the full admitted length minus one. -/
lemma prepared_wordLength (width : Nat) (positive : 1 ≤ width) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (accepted : admitted width state.1) :
    (ArithmeticAddress.runtimeCoefficientStep width positive state).2.1.toNat + 1 =
      wordLength width state.1 := by
  have actual := ArithmeticAddress.runtimeCoefficientStep_address_toNat
    width positive state clean zero accepted
  rw [actual]
  unfold admitted at accepted
  unfold wordLength
  split_ifs at accepted ⊢ <;> omega

private lemma window_congr (width left right : Nat) (same : left = right)
    (leftFits : left ≤ width + 3) (rightFits : right ≤ width + 3) :
    CoefficientCoordinates.window width left leftFits =
      CoefficientCoordinates.window width right rightFits := by
  subst right
  rfl

/-- All three actual native parts execute, including the complete preparation adjoint. -/
def program (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  PredicateCompute.program (ArithmeticAddress.runtimeCoefficientProgram width positive)
    (CoefficientWindow.program width signed)

/-- Disabled source control restores every original finite address and the entire input pool. -/
lemma program_apply_disabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (program width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  let prepared := ArithmeticAddress.runtimeCoefficientStep width positive state
  have workspace : prepared.2.2 = state.2.2 :=
    ArithmeticAddress.runtimeCoefficientStep_workspace width positive state
  have preparedClean := (congrArg Prod.fst workspace).trans clean
  have preparedZero := (congrArg Prod.snd workspace).trans zero
  have control : prepared.1.control = false :=
    (congrArg (fun value : Registers width => value.control)
      (ArithmeticAddress.runtimeCoefficientStep_source width positive state)).trans disabled
  have middle := CoefficientWindow.program_apply_disabled width signed environment prepared
    preparedClean preparedZero control
  exact PredicateCompute.program_apply_transformed_ket
    (ArithmeticAddress.runtimeCoefficientProgram width positive)
    (CoefficientWindow.program width signed)
    (ArithmeticAddress.runtimeCoefficientStep width positive) environment
    (ArithmeticAddress.runtimeCoefficientProgram_realizes width positive environment)
    state state middle

/-- Enabled arithmetic returns the complete original source result and cleans the entire pool. -/
lemma program_apply_enabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : state.1.control = true) (accepted : admitted width state.1) :
    (program width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (CoefficientWindowProgram.step
            (CoefficientCoordinates.window width (wordLength width state.1)
              (wordLength_fits width state.1 accepted))
            (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow) state.1,
              state.2))) := by
  let prepared := ArithmeticAddress.runtimeCoefficientStep width positive state
  let selected := CoefficientCoordinates.window width (wordLength width state.1)
    (wordLength_fits width state.1 accepted)
  let operation := if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow
  let transform := CoefficientWindowProgram.step selected operation
  let output := ArithmeticAddress.liftSource width transform state
  have workspace : prepared.2.2 = state.2.2 :=
    ArithmeticAddress.runtimeCoefficientStep_workspace width positive state
  have preparedClean := (congrArg Prod.fst workspace).trans clean
  have preparedZero := (congrArg Prod.snd workspace).trans zero
  have control : prepared.1.control = true :=
    (congrArg (fun value : Registers width => value.control)
      (ArithmeticAddress.runtimeCoefficientStep_source width positive state)).trans enabled
  have within := ArithmeticAddress.runtimeCoefficientStep_address_lt
    width positive state clean addressZero accepted
  have lengthEq := prepared_wordLength width positive state clean addressZero accepted
  have middle := CoefficientWindow.program_apply_original_window width positive signed
    environment prepared preparedClean preparedZero within
  rw [control, if_pos rfl] at middle
  have selectedSame := window_congr width (prepared.2.1.toNat + 1)
    (wordLength width state.1) lengthEq
    (lengthEq.le.trans (wordLength_fits width state.1 accepted))
    (wordLength_fits width state.1 accepted)
  rw [selectedSame] at middle
  have grouped : ArithmeticAddress.liftSource width transform prepared =
      ArithmeticAddress.runtimeCoefficientStep width positive output :=
    (CoefficientWindow.runtimeAddress_original_commute width positive selected operation state).symm
  have actual := middle.trans (congrArg
    (fun value : Data width => NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode value))) grouped)
  exact PredicateCompute.program_apply_transformed_ket
    (ArithmeticAddress.runtimeCoefficientProgram width positive)
    (CoefficientWindow.program width signed)
    (ArithmeticAddress.runtimeCoefficientStep width positive) environment
    (ArithmeticAddress.runtimeCoefficientProgram_realizes width positive environment)
    state output actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientAddress
