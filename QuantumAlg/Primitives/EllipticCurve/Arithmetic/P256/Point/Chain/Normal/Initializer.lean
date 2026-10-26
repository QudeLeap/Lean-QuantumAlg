/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Normal
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Division
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue

/-!
# Genuine normal preparation on the complete initialized call label

The actual predicate uses F560 and the original 256-bit X payload. Its
only label change is N837 XOR that predicate. The original source,
padding, small history, full pool, other stream top and address are
retained exactly, with no clean-N or clean-W hypothesis. The field
readout is a mathematical coordinate identity for the same real bits.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Normal

noncomputable section

open Arithmetic.Call Arithmetic.Call.Endpoint

attribute [local implicit_reducible] capacity width

private lemma step_eq_if (state : Window.Raw) :
    step state = if selected state then Window.normalBit.flip state else state := rfl

private lemma normal_flip_inputState (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Window.normalBit.flip (inputState stream width bounded input numerator flags address) =
      inputState stream width bounded input numerator (setNormal flags (!flags.2.1)) address :=
  (Control.toggle_normal_comm stream width bounded
    (clearedInitial input numerator flags address)).symm.trans
      (congrArg (Window.Enable.step stream width bounded)
        (normal_flip_clearedInitial input numerator flags address))

attribute [local irreducible] modulus

/-- The live enable is the original whole-digit predicate, with no normal-bit premise. -/
lemma inputState_flag (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Window.Enable.outputBit.get (inputState stream width bounded input numerator flags address) =
      divisionEnabled stream width bounded input numerator flags address :=
  inputState_enable stream width bounded input numerator flags address

/-- All binary X values are admitted; the three original padding positions are not tested. -/
lemma selected_inputState (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    selected (inputState stream width bounded input numerator flags address) =
      (divisionEnabled stream width bounded input numerator flags address &&
        !decide (input = 0)) := by
  rw [selected_value, inputState_flag, inputState_work2]
  have zero : Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input =
      (⟨0, Nat.two_pow_pos 256⟩ : Fin (2 ^ 256)) ↔ input = 0 := by
    constructor
    · intro same
      apply Fin.ext
      exact congrArg (fun value : Fin (2 ^ 256) => value.val) same
    · intro same
      apply Fin.ext
      exact congrArg (fun value : Fin (2 ^ modulus.size) => value.val) same
  simp only [zero]

/-- The whole original label is the same initializer with only its normal flag toggled. -/
lemma step_inputState (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    step (inputState stream width bounded input numerator flags address) =
      inputState stream width bounded input numerator
        (setNormal flags (flags.2.1 ^^
          (divisionEnabled stream width bounded input numerator flags address &&
            !decide (input = 0)))) address := by
  rw [step_eq_if, selected_inputState]
  cases active : (divisionEnabled stream width bounded input numerator flags address &&
      !decide (input = 0)) with
  | false =>
    rw [if_neg Bool.false_ne_true, Bool.xor_false]
    rfl
  | true =>
    rw [if_pos rfl, Bool.xor_true]
    exact normal_flip_inputState stream width bounded input numerator flags address

/-- A genuinely cleared pool disables this same normal toggle on every original binary word. -/
lemma selected_clearedInitial (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    selected (clearedInitial input numerator flags address) = false := by
  rw [selected_value,
    Window.Enable.outputBit_clean _ (initial_clean_pool input numerator flags), Bool.false_and]

lemma step_clearedInitial (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    step (clearedInitial input numerator flags address) =
      clearedInitial input numerator flags address := by
  rw [step_eq_if, selected_clearedInitial, if_neg Bool.false_ne_true]

/-- The actual enable inverse returns the complete initializer, retaining the new normal bit. -/
lemma clearEnable_step_inputState (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Window.Enable.step stream width bounded
        (step (inputState stream width bounded input numerator flags address)) =
      clearedInitial input numerator
        (setNormal flags (flags.2.1 ^^
          (divisionEnabled stream width bounded input numerator flags address &&
            !decide (input = 0)))) address := by
  rw [step_inputState, inputState_clear]

/-- The same actual predicate is the ordinary field nonzero test when X represents that value. -/
lemma selected_field (state : Window.Raw) (value : ZMod modulus)
    (represented : Frame.work2 state.1 = Residue.word value) :
    selected state = (Window.Enable.outputBit.get state && !decide (value = 0)) := by
  have zero : Residue.word value = (⟨0, Nat.two_pow_pos 256⟩ : Fin (2 ^ 256)) ↔ value = 0 := by
    constructor
    · intro same
      exact Residue.word_injective (same.trans Residue.word_zero.symm)
    · intro same
      exact (congrArg Residue.word same).trans Residue.word_zero
  rw [selected_value, represented]
  simp only [zero]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Normal
