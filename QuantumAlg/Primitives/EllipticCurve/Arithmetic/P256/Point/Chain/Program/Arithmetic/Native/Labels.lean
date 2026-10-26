/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Operator
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Division
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Initialized.Square
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Initialized.Reflect

/-!
# Complete field labels for the actual native arithmetic fragments

These mathematical labels describe the existing enable, square, normal
and reflection instructions. The genuine N update is an XOR for every
original N value; its cleanup specialization uses the same matched
predicate. No runtime operation or input restriction is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Arithmetic.Call Arithmetic.Call.Endpoint

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

local instance : NeZero modulus := ⟨Nat.ne_of_gt modulus_positive⟩

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus inputState clearedInitial Residue.input Residue.word

private lemma digit_predicate_congr {size : Nat} (first second : Fin size → Bool)
    (reads : ∀ index, first index = second index) :
    (!decide (∀ index, first index = false)) = (!decide (∀ index, second index = false)) := by
  have same : first = second := funext reads
  cases same
  rfl

private lemma digit_enabled_congr (stream : Fin 2) (size : Nat) (bounded : size ≤ 15)
    (first second : Window.Raw)
    (reads : ∀ index : Fin (size + 1),
      (Window.Enable.digitBit stream size bounded index).get first =
        (Window.Enable.digitBit stream size bounded index).get second) :
    Control.digitEnabled stream size bounded first =
      Control.digitEnabled stream size bounded second :=
  digit_predicate_congr
    (fun index : Fin (size + 1) => (Window.Enable.digitBit stream size bounded index).get first)
    (fun index : Fin (size + 1) => (Window.Enable.digitBit stream size bounded index).get second)
    reads

/-- The same actual whole-digit predicate on the original complete initialized source. -/
def nativeEnableValue (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) : Bool :=
  divisionEnabled parameters.stream (parameters.highRemaining + parameters.lowWidth)
    parameters.addressBound (Residue.input x) (Residue.input y) flags address

def nativeSquareValue (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) : ZMod modulus :=
  if parameters.nativeEnableValue x y flags address then x - y ^ 2 else x

def nativeNormalFlags (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) : Frame.Controls :=
  setNormal flags (flags.2.1 ^^
    (parameters.nativeEnableValue x y flags address && !decide (x = 0)))

def nativeReflectionValue (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) : ZMod modulus :=
  if parameters.nativeEnableValue x y flags address then -1 - x else x

private lemma residue_input_zero_iff (value : ZMod modulus) :
    Residue.input value = 0 ↔ value = 0 := by
  constructor
  · intro same
    have values := congrArg (fun word : Fin (2 ^ modulus.size) => word.val) same
    exact (ZMod.val_eq_zero value).mp ((Residue.input_val value).symm.trans values)
  · intro same
    apply Fin.ext
    exact (Residue.input_val value).trans
      ((congrArg (fun field : ZMod modulus => field.val) same).trans ZMod.val_zero)

/-- Numerical words do not change the real digit's C/W and address readout. -/
lemma nativeEnableValue_values (x y first second : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    parameters.nativeEnableValue x y flags address =
      parameters.nativeEnableValue first second flags address := by
  have reads (index : Fin (parameters.highRemaining + parameters.lowWidth + 1)) :
      (Window.Enable.digitBit parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound index).get
          (clearedInitial (Residue.input x) (Residue.input y) flags address) =
      (Window.Enable.digitBit parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound index).get
          (clearedInitial (Residue.input first) (Residue.input second) flags address) := by
    refine Fin.cases ?_ (fun digit => ?_) index
    · change (Window.streamBit parameters.stream).get _ =
        (Window.streamBit parameters.stream).get _
      unfold Window.streamBit
      split
      · change (clearedInitial (Residue.input x) (Residue.input y) flags address).1.2.1 =
          (clearedInitial (Residue.input first) (Residue.input second) flags address).1.2.1
        rw [clearedInitial_flags, clearedInitial_flags]
      · change (clearedInitial (Residue.input x) (Residue.input y) flags address).1.2.2.2 =
          (clearedInitial (Residue.input first) (Residue.input second) flags address).1.2.2.2
        rw [clearedInitial_flags, clearedInitial_flags]
    · change (Window.addressBit
        ⟨digit.val, lt_of_lt_of_le digit.isLt parameters.addressBound⟩).get _ =
        (Window.addressBit
          ⟨digit.val, lt_of_lt_of_le digit.isLt parameters.addressBound⟩).get _
      simp only [Window.addressBit_get, clearedInitial]
  exact digit_enabled_congr parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (clearedInitial (Residue.input x) (Residue.input y) flags address)
    (clearedInitial (Residue.input first) (Residue.input second) flags address) reads

lemma nativeEnableValue_setNormal (x y : ZMod modulus) (flags : Frame.Controls)
    (value : Bool) (address : Window.Address) :
    parameters.nativeEnableValue x y (setNormal flags value) address =
      parameters.nativeEnableValue x y flags address :=
  divisionEnabled_setNormal parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input x) (Residue.input y) flags value address

lemma nativeNormalFlags_enable (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    parameters.nativeEnableValue x y (parameters.nativeNormalFlags x y flags address) address =
      parameters.nativeEnableValue x y flags address :=
  parameters.nativeEnableValue_setNormal x y flags _ address

lemma nativeReflectionValue_normalFlags (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    parameters.nativeReflectionValue x y (parameters.nativeNormalFlags x y flags address) address =
      parameters.nativeReflectionValue x y flags address := by
  unfold nativeReflectionValue
  rw [parameters.nativeNormalFlags_enable]

/-- The existing normal program changes the same complete initializer by genuine N XOR. -/
lemma normalStep_inputState_field (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    Normal.step (inputState parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Residue.input x) (Residue.input y) flags address) =
      inputState parameters.stream (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound (Residue.input x) (Residue.input y)
        (parameters.nativeNormalFlags x y flags address) address := by
  have actual := Normal.step_inputState parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input x) (Residue.input y) flags address
  simpa only [nativeNormalFlags, nativeEnableValue, residue_input_zero_iff] using actual

/-- The actual inverse enable clears F while retaining precisely that genuine N XOR. -/
lemma clearNormalStep_inputState_field (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    Window.Enable.step parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Normal.step (inputState parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          (Residue.input x) (Residue.input y) flags address)) =
      clearedInitial (Residue.input x) (Residue.input y)
        (parameters.nativeNormalFlags x y flags address) address := by
  rw [parameters.normalStep_inputState_field, inputState_clear]

/-- Cleanup is a consequence of the same matched real predicate, with no clean-N premise. -/
lemma nativeNormalFlags_of_match (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address)
    (matched : flags.2.1 =
      (parameters.nativeEnableValue x y flags address && !decide (x = 0))) :
    parameters.nativeNormalFlags x y flags address = setNormal flags false := by
  unfold nativeNormalFlags
  rw [matched, Bool.xor_self]

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
