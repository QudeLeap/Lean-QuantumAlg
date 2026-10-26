/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Correctness
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Horner

/-! # Canonical full-word invariant for the actual selected Horner schedule -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner

open ModularAddition

/-- The original clean target word. -/
def zeroWord : Word := ⟨0, Nat.two_pow_pos width⟩

lemma zeroWord_canonical : Canonical zeroWord := modulus_positive

lemma doubledWord_zero : Doubling.doubledWord zeroWord = zeroWord := by
  apply Fin.ext
  exact Nat.zero_mod modulus

private lemma prefix_bound (source multiplier : Nat) (processed : Nat) :
    Nat.FixedWidth.ModularHorner.hornerPrefix modulus source multiplier width processed <
      modulus := by
  cases processed with
  | zero => exact modulus_positive
  | succ processed => exact Nat.mod_lt _ modulus_positive

/-- The high multiplier prefix, masked by the unchanged original quantum outer selector. -/
def prefixWord (source multiplier : Word) (selected : Bool) (processed : Nat) : Word :=
  ⟨Nat.FixedWidth.ModularHorner.hornerPrefix modulus source.val
      (if selected then multiplier.val else 0) width processed,
    (prefix_bound _ _ processed).trans modulus_lt_capacity⟩

lemma prefixWord_canonical (source multiplier : Word) (selected : Bool) (processed : Nat) :
    Canonical (prefixWord source multiplier selected processed) := prefix_bound _ _ processed

lemma prefixWord_zero (source multiplier : Word) (selected : Bool) :
    prefixWord source multiplier selected 0 = zeroWord := Fin.ext rfl

private lemma selected_step (modulus source target multiplier index : Nat) (selected : Bool) :
    (2 * target + ((if selected then multiplier else 0).testBit index).toNat * source) %
        modulus =
      if selected && multiplier.testBit index then (source + (2 * target) % modulus) % modulus
      else (2 * target) % modulus := by
  cases selected with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.toNat_false,
      Nat.zero_mul, Nat.add_zero, Bool.false_and]
  | true =>
      simp only [↓reduceIte, Bool.true_and]
      cases bit : multiplier.testBit index with
      | false => simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero,
          Bool.false_eq_true, ↓reduceIte]
      | true => simp only [Bool.toNat_true, Nat.one_mul, ↓reduceIte,
          Nat.add_mod_mod, Nat.add_comm]

private lemma conditional_value {bound : Nat} (selected : Bool) (yes no : Fin bound) :
    (if selected then yes else no).val = if selected then yes.val else no.val := by
  cases selected <;> rfl

/-- A target doubling followed by the selected actual add agrees with the next prefix. -/
lemma prefixWord_succ (source multiplier : Word) (selected : Bool) (processed : Nat) :
    prefixWord source multiplier selected (processed + 1) =
      if selected && multiplier.val.testBit (width - processed - 1) then
        modularSumWord source (Doubling.doubledWord
          (prefixWord source multiplier selected processed))
      else Doubling.doubledWord (prefixWord source multiplier selected processed) := by
  apply Fin.ext
  rw [conditional_value]
  exact selected_step modulus source.val
    (prefixWord source multiplier selected processed).val multiplier.val
    (width - processed - 1) selected

/-- Reading all original multiplier bits yields the selected modular product. -/
lemma prefixWord_full (source multiplier : Word) (selected : Bool) :
    (prefixWord source multiplier selected width).val =
      if selected then (multiplier.val * source.val) % modulus else 0 := by
  have bound : (if selected then multiplier.val else 0) < 2 ^ width := by
    cases selected with
    | false => exact Nat.two_pow_pos width
    | true => exact multiplier.isLt
  have full := Nat.FixedWidth.ModularHorner.prefix_full modulus source.val
    (if selected then multiplier.val else 0) width bound
  change Nat.FixedWidth.ModularHorner.hornerPrefix modulus source.val
    (if selected then multiplier.val else 0) width width = _
  exact full.trans (by cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Nat.zero_mul, Nat.zero_mod])

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Horner
