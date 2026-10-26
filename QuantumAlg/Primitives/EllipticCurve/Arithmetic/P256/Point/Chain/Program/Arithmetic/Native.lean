/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Arithmetic.Native.Labels

/-!
# Exact original-bank actions of the native arithmetic prefix and tail

The products below follow the existing point instructions: enable,
square subtraction and normal preparation; then, after the exceptional
query, enable, inverse normal, reflection and clear. Every factor is the
same placed native operator beside the unchanged arbitrary reference.
Complete initialized labels retain all padding, small history, pool,
C/N/W and address systems. The genuine N update is an arbitrary XOR.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Arithmetic.Call Arithmetic.Call.Endpoint

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

local instance : NeZero modulus := ⟨Nat.ne_of_gt modulus_positive⟩

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus inputState clearedInitial Residue.input Residue.word
attribute [local irreducible] nativeOperator referenceKet
attribute [local irreducible] Normal.program Normal.inverseProgram

private lemma native_chain_three {R : Register} (first second third : HilbertOperator R)
    (initial prepared updated final : HilbertVector R)
    (one : first.applyVec initial = prepared)
    (two : second.applyVec prepared = updated)
    (three : third.applyVec updated = final) :
    HilbertOperator.applyVec (third * (second * first)) initial = final := by
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, one, two, three]

private lemma native_chain_four {R : Register} (first second third fourth : HilbertOperator R)
    (initial prepared updated reflected final : HilbertVector R)
    (one : first.applyVec initial = prepared)
    (two : second.applyVec prepared = updated)
    (three : third.applyVec updated = reflected)
    (four : fourth.applyVec reflected = final) :
    HilbertOperator.applyVec (fourth * (third * (second * first))) initial = final := by
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
    HilbertOperator.mul_applyVec, one, two, three, four]

private lemma native_label_action {R : Register} {Label : Type}
    (ket : Label → HilbertVector R) (operator : HilbertOperator R)
    (initial intermediate final : Label)
    (actual : operator.applyVec (ket initial) = ket intermediate)
    (same : intermediate = final) :
    operator.applyVec (ket initial) = ket final :=
  actual.trans (congrArg ket same)

/-- The actual multiplication prefix, with exactly one existing enable instruction. -/
def multiplicationNativePrefixOperator (environment : OracleModel.empty.Interpretation)
    (Reference : Register) : HilbertOperator (ctx.register.prod Reference) :=
  parameters.nativeOperator Normal.program environment Reference *
    (parameters.nativeOperator
      (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram) environment Reference *
     parameters.nativeOperator
      (Window.Enable.program parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
      environment Reference)

/-- The actual reflection tail, including its own inverse enable. -/
def reflectionNativeTailOperator (environment : OracleModel.empty.Interpretation)
    (Reference : Register) : HilbertOperator (ctx.register.prod Reference) :=
  parameters.nativeOperator
    (Window.Enable.inverseProgram parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
    environment Reference *
    (parameters.nativeOperator (Window.suffixProgram Arithmetic.Reflect.program)
      environment Reference *
     (parameters.nativeOperator Normal.inverseProgram environment Reference *
      parameters.nativeOperator
        (Window.Enable.program parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
        environment Reference))

private lemma native_enable_initialized (environment : OracleModel.empty.Interpretation)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator
      (Window.Enable.program parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
      environment Reference).applyVec
        (parameters.referenceKet
          (clearedInitial (Residue.input x) (Residue.input y) flags address) reference) =
      parameters.referenceKet (inputState parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Residue.input x) (Residue.input y) flags address) reference := by
  exact native_label_action (fun state => parameters.referenceKet state reference) _ _ _ _
    (parameters.nativeOperator_original _ environment _ _
      (Window.Enable.program_ket parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound environment _)
      reference)
    (inputState_eq parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound (Residue.input x) (Residue.input y) flags address).symm

private lemma native_clear_initialized (environment : OracleModel.empty.Interpretation)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator
      (Window.Enable.inverseProgram parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
      environment Reference).applyVec
        (parameters.referenceKet (inputState parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          (Residue.input x) (Residue.input y) flags address) reference) =
      parameters.referenceKet
        (clearedInitial (Residue.input x) (Residue.input y) flags address) reference := by
  exact native_label_action (fun state => parameters.referenceKet state reference) _ _ _ _
    (parameters.nativeOperator_original _ environment _ _
      (Window.Enable.inverseProgram_ket parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound environment _)
      reference)
    (inputState_clear parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound (Residue.input x) (Residue.input y) flags address)

private lemma native_normal_initialized
    (environment : OracleModel.empty.Interpretation) (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator Normal.program
      environment Reference).applyVec
        (parameters.referenceKet (inputState parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          (Residue.input x) (Residue.input y) flags address) reference) =
      parameters.referenceKet (inputState parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Residue.input x) (Residue.input y)
        (parameters.nativeNormalFlags x y flags address) address) reference := by
  exact native_label_action (fun state => parameters.referenceKet state reference) _ _ _ _
    (parameters.nativeOperator_original _ environment _ _
      (Normal.program_apply environment _) reference)
    (parameters.normalStep_inputState_field x y flags address)

private lemma native_inverse_normal_initialized
    (environment : OracleModel.empty.Interpretation) (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator Normal.inverseProgram environment Reference).applyVec
        (parameters.referenceKet (inputState parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          (Residue.input x) (Residue.input y) flags address) reference) =
      parameters.referenceKet (inputState parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Residue.input x) (Residue.input y)
        (parameters.nativeNormalFlags x y flags address) address) reference := by
  exact native_label_action (fun state => parameters.referenceKet state reference) _ _ _ _
    (parameters.nativeOperator_original _ environment _ _
      (Normal.inverseProgram_apply environment _) reference)
    (parameters.normalStep_inputState_field x y flags address)

/-- Existing square and normal instructions return one complete live-enable initializer. -/
lemma multiplicationNativePrefixOperator_field (environment : OracleModel.empty.Interpretation)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.multiplicationNativePrefixOperator environment Reference).applyVec
        (parameters.referenceKet
          (clearedInitial (Residue.input x) (Residue.input y) flags address) reference) =
      parameters.referenceKet (inputState parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Residue.input (parameters.nativeSquareValue x y flags address)) (Residue.input y)
        (parameters.nativeNormalFlags (parameters.nativeSquareValue x y flags address)
          y flags address) address) reference := by
  have enabled := parameters.native_enable_initialized environment x y flags address reference
  have squared := parameters.nativeOperator_original
    (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram) environment _ _
    (Window.Initialized.subtractSquareProgram_inputState environment parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound x y flags address)
    reference
  have normal := parameters.native_normal_initialized environment
    (parameters.nativeSquareValue x y flags address) y flags address reference
  exact native_chain_three _ _ _ _ _ _ _ enabled squared normal

/-- Original N may be either value; the real inverse normal toggles the same genuine predicate. -/
lemma reflectionNativeTailOperator_field (environment : OracleModel.empty.Interpretation)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.reflectionNativeTailOperator environment Reference).applyVec
        (parameters.referenceKet
          (clearedInitial (Residue.input x) (Residue.input y) flags address) reference) =
      parameters.referenceKet
        (clearedInitial (Residue.input (parameters.nativeReflectionValue x y flags address))
          (Residue.input y) (parameters.nativeNormalFlags x y flags address) address)
        reference := by
  have enabled := parameters.native_enable_initialized environment x y flags address reference
  have normal := parameters.native_inverse_normal_initialized environment
    x y flags address reference
  have reflected := parameters.nativeOperator_original
    (Window.suffixProgram Arithmetic.Reflect.program) environment _ _
    (Window.Initialized.reflectionProgram_inputState environment parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound x y
      (parameters.nativeNormalFlags x y flags address) address) reference
  have same :
      inputState parameters.stream (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound
        (Residue.input (parameters.nativeReflectionValue x y
          (parameters.nativeNormalFlags x y flags address) address)) (Residue.input y)
        (parameters.nativeNormalFlags x y flags address) address =
      inputState parameters.stream (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound (Residue.input (parameters.nativeReflectionValue x y flags address))
        (Residue.input y) (parameters.nativeNormalFlags x y flags address) address :=
    congrArg (fun value => inputState parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (Residue.input value) (Residue.input y)
      (parameters.nativeNormalFlags x y flags address) address)
      (parameters.nativeReflectionValue_normalFlags x y flags address)
  have reflection := native_label_action (fun state => parameters.referenceKet state reference)
    _ _ _ _ reflected same
  have cleared := parameters.native_clear_initialized environment
    (parameters.nativeReflectionValue x y flags address) y
    (parameters.nativeNormalFlags x y flags address) address reference
  exact native_chain_four _ _ _ _ _ _ _ _ _ enabled normal reflection cleared

/-- The matched normal predicate clears N internally; the general tail law remains unrestricted. -/
lemma reflectionNativeTailOperator_field_matched (environment : OracleModel.empty.Interpretation)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (matched : flags.2.1 =
      (parameters.nativeEnableValue x y flags address && !decide (x = 0)))
    {Reference : Register} (reference : Reference.Index) :
    (parameters.reflectionNativeTailOperator environment Reference).applyVec
        (parameters.referenceKet
          (clearedInitial (Residue.input x) (Residue.input y) flags address) reference) =
      parameters.referenceKet
        (clearedInitial (Residue.input (parameters.nativeReflectionValue x y flags address))
          (Residue.input y) (setNormal flags false) address) reference := by
  exact native_label_action (fun state => parameters.referenceKet state reference) _ _ _ _
    (parameters.reflectionNativeTailOperator_field environment x y flags address reference)
    (congrArg (fun updated => clearedInitial
      (Residue.input (parameters.nativeReflectionValue x y flags address))
      (Residue.input y) updated address)
      (parameters.nativeNormalFlags_of_match x y flags address matched))

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
