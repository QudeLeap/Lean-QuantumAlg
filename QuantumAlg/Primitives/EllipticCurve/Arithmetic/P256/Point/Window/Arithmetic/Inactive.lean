/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Initialized
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Square
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Reflect

/-!
# Disabled native arithmetic retains arbitrary original binary words

These are actions of the unchanged actual native programs. A false real
whole-digit enable needs no canonicality of either original word. The
initialized-label consumers discharge A-zero and the three arithmetic
flags internally, retain arbitrary original N/W and every other system,
and do not equate an identity action with a free or skipped program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Inactive

noncomputable section

open EncodedBit.WindowLookup Chain.Arithmetic.Call Chain.Arithmetic.Call.Endpoint

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus inputState clearedInitial ket
attribute [local irreducible] Chain.Normal.program Chain.Normal.inverseProgram

private lemma not_decide_false {statement : Prop} [Decidable statement]
    (disabled : (!decide statement) = false) : statement := by
  by_cases chosen : statement
  · exact chosen
  · simp [chosen] at disabled

private lemma original_target_self (state : Raw) :
    resultSetConstant (resultWord .work2) (Frame.work2 state.1) state = state := by
  apply resultSetConstant_self encoding_surjective (resultWord .work2)
    (resultWord_distinct .work2)
  intro index
  change (pointBit (WordPort.bit .work2 index)).get state = _
  rw [pointBit_get, WordPort.bit_get]
  rfl

/-- This uses the original full digit, including its retained top bit. -/
lemma enable_step_disabled (stream : Fin 2) (size : Nat) (bounded : size ≤ 15)
    (state : Raw) (disabled : Chain.Control.digitEnabled stream size bounded state = false) :
    Enable.step stream size bounded state = state := by
  have allZero : ∀ index : Fin (size + 1),
      (Enable.digitBit stream size bounded index).get state = false :=
    not_decide_false disabled
  change (if ∀ index : Fin (size + 1),
    (Enable.digitBit stream size bounded index).get state = false
    then state else Enable.outputBit.flip state) = state
  exact if_pos allZero

/-- The live initializer equals the original complete cleared label on a zero digit. -/
lemma inputState_disabled (stream : Fin 2) (size : Nat) (bounded : size ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Address)
    (disabled : divisionEnabled stream size bounded input numerator flags address = false) :
    inputState stream size bounded input numerator flags address =
      clearedInitial input numerator flags address :=
  (inputState_eq stream size bounded input numerator flags address).trans
    (enable_step_disabled stream size bounded
      (clearedInitial input numerator flags address) disabled)

/-- A false real F keeps every original bit, with arbitrary binary source and multiplier. -/
lemma square_program_disabled (environment : OracleModel.empty.Interpretation) (state : Raw)
    (flags : ((Placement.layout Native.squarePorts).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Native.squarePorts).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Native.squarePorts).grouping state.1).1.2.2 = false)
    (zero : Frame.work1 state.1 = Horner.zeroWord)
    (disabled : Native.BorrowedControl.flag.get state.1 = false) :
    (suffixProgram Native.BorrowedControl.subtractSquareProgram).applyNormalized environment
        (ket state) = ket state := by
  have selected : (Native.BorrowedControl.controlBit Native.squarePorts).get
      ((Placement.layout Native.squarePorts).grouping state.1).2.2 = false :=
    (Native.BorrowedControl.controlBit_get Native.squarePorts state.1).trans disabled
  have sourceAdmitted : (Native.BorrowedControl.controlBit Native.squarePorts).get
      ((Placement.layout Native.squarePorts).grouping state.1).2.2 = true →
        Canonical (Frame.numerator state.1) := by
    intro active
    have impossible := selected.symm.trans active
    cases impossible
  have targetAdmitted : (Native.BorrowedControl.controlBit Native.squarePorts).get
      ((Placement.layout Native.squarePorts).grouping state.1).2.2 = true →
        Canonical (Frame.work2 state.1) := by
    intro active
    have impossible := selected.symm.trans active
    cases impossible
  have actual := subtractSquareProgram_original_label environment state flags zero
    sourceAdmitted targetAdmitted
  have same : Accumulate.Inverse.differenceWord (Frame.numerator state.1)
      (Frame.numerator state.1) (Frame.work2 state.1)
      ((Native.BorrowedControl.controlBit Native.squarePorts).get
        ((Placement.layout Native.squarePorts).grouping state.1).2.2) = Frame.work2 state.1 := by
    rw [selected]
    rfl
  exact actual.trans (congrArg ket
    ((congrArg (fun value => resultSetConstant (resultWord .work2) value state) same).trans
      (original_target_self state)))

lemma normal_step_disabled (state : Raw)
    (disabled : Native.BorrowedControl.flag.get state.1 = false) :
    Chain.Normal.step state = state := by
  have output : Enable.outputBit.get state = false :=
    (Chain.Control.flag_get state).trans disabled
  have selected : Chain.Normal.selected state = false := by
    rw [Chain.Normal.selected_value, output]
    rfl
  rw [Chain.Normal.step_eq_if, selected]
  rfl

lemma normal_program_disabled (environment : OracleModel.empty.Interpretation) (state : Raw)
    (disabled : Native.BorrowedControl.flag.get state.1 = false) :
    Chain.Normal.program.applyNormalized environment (ket state) = ket state :=
  (Chain.Normal.program_apply environment state).trans
    (congrArg ket (normal_step_disabled state disabled))

lemma inverse_normal_program_disabled (environment : OracleModel.empty.Interpretation)
    (state : Raw) (disabled : Native.BorrowedControl.flag.get state.1 = false) :
    Chain.Normal.inverseProgram.applyNormalized environment (ket state) = ket state :=
  (Chain.Normal.inverseProgram_apply environment state).trans
    (congrArg ket (normal_step_disabled state disabled))

/-- The physical reflection keeps arbitrary binary X when its actual retained enable is false. -/
lemma reflection_program_disabled (environment : OracleModel.empty.Interpretation) (state : Raw)
    (zero : Frame.work1 state.1 = MAU.Addition.TTK.Reflection.zero 256)
    (disabled : Native.BorrowedControl.flag.get state.1 = false) :
    (suffixProgram Chain.Arithmetic.Reflect.program).applyNormalized environment
        (ket state) = ket state := by
  have actual := reflectionProgram_original_label environment state zero
  have same : Frame.work2 (Chain.Arithmetic.Reflect.step state.1) = Frame.work2 state.1 := by
    rw [Chain.Arithmetic.Reflect.step_work2, disabled]
    rfl
  exact actual.trans (congrArg ket
    ((congrArg (fun value => resultSetConstant (resultWord .work2) value state) same).trans
      (original_target_self state)))

lemma square_inputState_disabled (environment : OracleModel.empty.Interpretation)
    (stream : Fin 2) (size : Nat) (bounded : size ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Address)
    (disabled : divisionEnabled stream size bounded input numerator flags address = false) :
    (suffixProgram Native.BorrowedControl.subtractSquareProgram).applyNormalized environment
        (ket (inputState stream size bounded input numerator flags address)) =
      ket (inputState stream size bounded input numerator flags address) :=
  square_program_disabled environment _
    (Initialized.inputState_arithmeticFlags Native.squarePorts stream size bounded
      input numerator flags address)
    (inputState_work1 stream size bounded input numerator flags address)
    ((Initialized.inputState_flag stream size bounded input numerator flags address).trans disabled)

lemma normal_inputState_disabled (environment : OracleModel.empty.Interpretation)
    (stream : Fin 2) (size : Nat) (bounded : size ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Address)
    (disabled : divisionEnabled stream size bounded input numerator flags address = false) :
    Chain.Normal.program.applyNormalized environment
        (ket (inputState stream size bounded input numerator flags address)) =
      ket (inputState stream size bounded input numerator flags address) :=
  normal_program_disabled environment _
    ((Initialized.inputState_flag stream size bounded input numerator flags address).trans disabled)

lemma inverse_normal_inputState_disabled (environment : OracleModel.empty.Interpretation)
    (stream : Fin 2) (size : Nat) (bounded : size ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Address)
    (disabled : divisionEnabled stream size bounded input numerator flags address = false) :
    Chain.Normal.inverseProgram.applyNormalized environment
        (ket (inputState stream size bounded input numerator flags address)) =
      ket (inputState stream size bounded input numerator flags address) :=
  inverse_normal_program_disabled environment _
    ((Initialized.inputState_flag stream size bounded input numerator flags address).trans disabled)

lemma reflection_inputState_disabled (environment : OracleModel.empty.Interpretation)
    (stream : Fin 2) (size : Nat) (bounded : size ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Address)
    (disabled : divisionEnabled stream size bounded input numerator flags address = false) :
    (suffixProgram Chain.Arithmetic.Reflect.program).applyNormalized environment
        (ket (inputState stream size bounded input numerator flags address)) =
      ket (inputState stream size bounded input numerator flags address) :=
  reflection_program_disabled environment _
    (inputState_work1 stream size bounded input numerator flags address)
    ((Initialized.inputState_flag stream size bounded input numerator flags address).trans disabled)

end

end Inactive

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
