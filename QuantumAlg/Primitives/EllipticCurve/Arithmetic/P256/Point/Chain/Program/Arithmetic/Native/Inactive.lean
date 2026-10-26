/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Arithmetic.Native
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Inactive

/-!
# Actual native arithmetic fragments on the arbitrary binary disabled sector

The original complete zero-digit label is fixed by the unchanged native
prefix and tail, beside arbitrary external Reference. X and Y are any
binary words, while original N/W remain arbitrary. The same real enable,
square, normal, reflection and clear operators execute with their full
existing gate costs; their identity action does not remove instructions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Arithmetic.Call Arithmetic.Call.Endpoint

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus inputState clearedInitial nativeOperator referenceKet
attribute [local irreducible] Normal.program Normal.inverseProgram

private lemma native_enable_binary_initialized (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator
      (Window.Enable.program parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
      environment Reference).applyVec
        (parameters.referenceKet (clearedInitial input numerator flags address) reference) =
      parameters.referenceKet (inputState parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        input numerator flags address) reference := by
  exact native_label_action (fun state => parameters.referenceKet state reference) _ _ _ _
    (parameters.nativeOperator_original _ environment _ _
      (Window.Enable.program_ket parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound environment _)
      reference)
    (inputState_eq parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound input numerator flags address).symm

private lemma native_clear_binary_initialized (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator
      (Window.Enable.inverseProgram parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
      environment Reference).applyVec
        (parameters.referenceKet (inputState parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          input numerator flags address) reference) =
      parameters.referenceKet (clearedInitial input numerator flags address) reference := by
  exact native_label_action (fun state => parameters.referenceKet state reference) _ _ _ _
    (parameters.nativeOperator_original _ environment _ _
      (Window.Enable.inverseProgram_ket parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound environment _)
      reference)
    (inputState_clear parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound input numerator flags address)

/-- Every original source, padding, pool, C/N/W and address system is retained exactly. -/
lemma multiplicationNativePrefixOperator_disabled
    (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    (disabled : divisionEnabled parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      input numerator flags address = false)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.multiplicationNativePrefixOperator environment Reference).applyVec
        (parameters.referenceKet (clearedInitial input numerator flags address) reference) =
      parameters.referenceKet (clearedInitial input numerator flags address) reference := by
  have enabled := parameters.native_enable_binary_initialized environment
    input numerator flags address reference
  have squared := parameters.nativeOperator_original
    (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram) environment _ _
    (Window.Inactive.square_inputState_disabled environment parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      input numerator flags address disabled) reference
  have normal := parameters.nativeOperator_original Normal.program environment _ _
    (Window.Inactive.normal_inputState_disabled environment parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      input numerator flags address disabled) reference
  have combined := native_chain_three (R := ctx.register.prod Reference)
    _ _ _ _ _ _ _ enabled squared normal
  exact native_label_action (fun state => parameters.referenceKet state reference) _ _ _ _ combined
    (Window.Inactive.inputState_disabled parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      input numerator flags address disabled)

/-- Inverse normal does not require clean original N in the disabled sector. -/
lemma reflectionNativeTailOperator_disabled (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    (disabled : divisionEnabled parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      input numerator flags address = false)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.reflectionNativeTailOperator environment Reference).applyVec
        (parameters.referenceKet (clearedInitial input numerator flags address) reference) =
      parameters.referenceKet (clearedInitial input numerator flags address) reference := by
  have enabled := parameters.native_enable_binary_initialized environment
    input numerator flags address reference
  have normal := parameters.nativeOperator_original Normal.inverseProgram environment _ _
    (Window.Inactive.inverse_normal_inputState_disabled environment parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      input numerator flags address disabled) reference
  have reflected := parameters.nativeOperator_original
    (Window.suffixProgram Arithmetic.Reflect.program) environment _ _
    (Window.Inactive.reflection_inputState_disabled environment parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      input numerator flags address disabled) reference
  have cleared := parameters.native_clear_binary_initialized environment
    input numerator flags address reference
  exact native_chain_four _ _ _ _ _ _ _ _ _ enabled normal reflected cleared

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
