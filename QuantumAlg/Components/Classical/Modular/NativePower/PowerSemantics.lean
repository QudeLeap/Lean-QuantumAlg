/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Bit.Semantics
import all QuantumAlg.Util.Classical.Modular.Pow

/-!
# Original modular-power semantics of the actual finite-word recurrence

The existing intrinsic modular model supplies the most-significant-bit prefix
invariant. Exact full-product reduction realizes that same recurrence on raw
stored words. Visiting the declared finite exponent slots therefore yields
the original modular power, including the empty exponent and leading zeros.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open ClassicalAlgorithms.Modular

/-- Encode an intrinsically canonical residue in its exact declared word width. -/
def residueValue {width : Nat} {spec : ModulusSpec width} (value : Residue spec) :
    CShape.Word width :=
  .unsignedWord value.toWord

private theorem word_eq_of_toNat_eq {width : Nat} (left right : CShape.Word width)
    (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | unsignedWord left =>
      cases right with
      | unsignedWord right => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- Actual full-product reduction coincides with intrinsic canonical multiplication. -/
theorem nativePower_multiplyValue_residue {width : Nat} (spec : ModulusSpec width)
    (left right : Residue spec) :
    multiplyValue (residueValue left) (residueValue right) (.unsignedWord spec.extendedWord) =
      residueValue (Mul.eval spec ⟨left, right⟩) := by
  apply word_eq_of_toNat_eq
  rw [nativePower_multiplyValue_spec]
  exact (Mul.modularMul_eval_val spec ⟨left, right⟩).symm

/-- The actual full-product square has the intrinsic square's canonical value. -/
theorem nativePower_squareValue_residue {width : Nat} (spec : ModulusSpec width)
    (value : Residue spec) :
    multiplyValue (residueValue value) (residueValue value) (.unsignedWord spec.extendedWord) =
      residueValue (Square.eval spec value) := by
  apply word_eq_of_toNat_eq
  rw [nativePower_multiplyValue_spec]
  exact (Square.modularSquare_eval_val spec value).symm

/-- Each actual bit recurrence is the source's same left-to-right modular-power step. -/
theorem nativePower_bitValue_residue {width : Nat} (spec : ModulusSpec width)
    (base accumulator : Residue spec) (bit : Bool) :
    bitValue (residueValue base) (.unsignedWord spec.extendedWord) (residueValue accumulator)
        bit = residueValue (Pow.msbStep spec base accumulator bit) := by
  cases bit
  · simp only [bitValue, Pow.msbStep, Bool.false_eq_true, if_false]
    exact nativePower_squareValue_residue spec accumulator
  · simp only [bitValue, Pow.msbStep, if_true]
    rw [nativePower_squareValue_residue, nativePower_multiplyValue_residue]

/-- One genuine exponent slot advances the existing source prefix invariant. -/
theorem nativePower_bitValue_prefix {width exponentWidth : Nat} (spec : ModulusSpec width)
    (input : Pow.Input spec exponentWidth) (index : Fin exponentWidth) :
    bitValue (residueValue input.base) (.unsignedWord spec.extendedWord)
        (residueValue (Pow.partialEval spec input index.val))
        (Pow.exponentBit input.exponent index) =
      residueValue (Pow.partialEval spec input (index.val + 1)) := by
  rw [nativePower_bitValue_residue, Pow.modularPow_msbStep_partialEval]

private theorem bitValue_fold {width count : Nat}
    (base : CShape.Word width) (modulus : CShape.Word (width + 1))
    (bits : Fin count → Bool) (states : Fin (count + 1) → CShape.Word width)
    (steps : ∀ index : Fin count,
      bitValue base modulus (states index.castSucc) (bits index) = states index.succ) :
    (List.ofFn bits).foldl (bitValue base modulus) (states 0) = states (Fin.last count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have first := steps (0 : Fin (count + 1))
      simp only [Fin.castSucc_zero] at first
      rw [List.ofFn_succ, List.foldl_cons, first]
      exact ih (fun index => bits index.succ) (fun index => states index.succ)
        (fun index => steps index.succ)

/-- The actual finite-word recurrence on every declared exponent slot returns the original power. -/
theorem nativePower_math_fold {width exponentWidth : Nat} (spec : ModulusSpec width)
    (input : Pow.Input spec exponentWidth) :
    (List.ofFn (Pow.exponentBit input.exponent)).foldl
        (bitValue (residueValue input.base) (.unsignedWord spec.extendedWord))
        (residueValue (Residue.one spec)) = residueValue (Pow.eval spec input) := by
  have actual := bitValue_fold (residueValue input.base) (.unsignedWord spec.extendedWord)
    (Pow.exponentBit input.exponent)
    (fun index : Fin (exponentWidth + 1) => residueValue (Pow.partialEval spec input index.val))
    (fun index => nativePower_bitValue_prefix spec input index)
  simpa only [Fin.val_zero, Fin.val_last, Pow.modularPow_partialEval_zero,
    Pow.modularPow_partialEval_final] using actual

end QuantumAlg.ClassicalRoutines.Modular.NativePower
