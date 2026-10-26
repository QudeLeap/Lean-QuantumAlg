/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Arithmetic
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate

/-! # Full-word invariant for selected multiply-accumulate and actual source restoration -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

open ModularAddition

/-- The original source after each actually paid modular doubling. -/
def sourceWord (source : Word) : Nat → Word
  | 0 => source
  | index + 1 => Doubling.doubledWord (sourceWord source index)

lemma sourceWord_canonical (source : Word) (canonical : Canonical source) (index : Nat) :
    Canonical (sourceWord source index) := by
  cases index with
  | zero => exact canonical
  | succ index => exact Doubling.doubledWord_canonical _

private lemma doubled_residue (modulus source index : Nat) :
    (2 * ((2 ^ index * source) % modulus)) % modulus =
      (2 ^ (index + 1) * source) % modulus := by
  rw [Nat.mul_mod_mod]
  apply congrArg (fun value => value % modulus)
  rw [Nat.pow_succ]
  ac_rfl

lemma sourceWord_value (source : Word) (canonical : Canonical source) (index : Nat) :
    (sourceWord source index).val = (2 ^ index * source.val) % modulus := by
  induction index with
  | zero =>
      simpa only [sourceWord, Nat.pow_zero, Nat.one_mul] using
        (Nat.mod_eq_of_lt canonical).symm
  | succ index ih =>
      change (2 * (sourceWord source index).val) % modulus = _
      rw [ih]
      exact doubled_residue modulus source.val index

/-- A canonical accumulator prefix, with no zero-entry requirement on the original target. -/
def accumulatorWord (source multiplier target : Word) (selected : Bool) (processed : Nat) : Word :=
  ⟨Nat.FixedWidth.ModularAccumulate.accumulateSelected modulus source.val
      (if selected then multiplier.val else 0) target.val processed,
    (Nat.FixedWidth.ModularAccumulate.accumulateSelected_lt modulus_positive).trans
      modulus_lt_capacity⟩

lemma accumulatorWord_canonical (source multiplier target : Word) (selected : Bool)
    (processed : Nat) :
    Canonical (accumulatorWord source multiplier target selected processed) :=
  Nat.FixedWidth.ModularAccumulate.accumulateSelected_lt modulus_positive

lemma accumulatorWord_zero (source multiplier target : Word) (selected : Bool)
    (canonical : Canonical target) :
    accumulatorWord source multiplier target selected 0 = target :=
  Fin.ext (Nat.mod_eq_of_lt canonical)

private lemma contribution (modulus source multiplier index : Nat) (selected : Bool) :
    Nat.FixedWidth.ModularAccumulate.selectedBitContribution modulus source
        (if selected then multiplier else 0) index =
      if selected && multiplier.testBit index then (2 ^ index * source) % modulus else 0 := by
  rw [Nat.FixedWidth.ModularAccumulate.selectedBitContribution_eq_if]
  cases selected with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.false_and]
  | true => simp only [↓reduceIte, Bool.true_and,
      Nat.FixedWidth.ModularAccumulate.stageConstantResidue, Nat.mul_comm]

private lemma conditional_value {bound : Nat} (selected : Bool) (yes no : Fin bound) :
    (if selected then yes else no).val = if selected then yes.val else no.val := by
  cases selected <;> rfl

/-- One actual selected add of the doubled original source advances the low-bit prefix. -/
lemma accumulatorWord_succ (source multiplier target : Word) (selected : Bool)
    (canonical : Canonical source) (index : Nat) :
    accumulatorWord source multiplier target selected (index + 1) =
      if selected && multiplier.val.testBit index then
        modularSumWord (sourceWord source index)
          (accumulatorWord source multiplier target selected index)
      else accumulatorWord source multiplier target selected index := by
  apply Fin.ext
  rw [conditional_value]
  change Nat.FixedWidth.ModularAccumulate.accumulateSelected modulus source.val
    (if selected then multiplier.val else 0) target.val (index + 1) = _
  rw [Nat.FixedWidth.ModularAccumulate.accumulateSelected_succ, contribution]
  change ((accumulatorWord source multiplier target selected index).val +
    (if selected && multiplier.val.testBit index then (2 ^ index * source.val) % modulus
      else 0)) % modulus = _
  cases bit : selected && multiplier.val.testBit index with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact Nat.mod_eq_of_lt (accumulatorWord_canonical source multiplier target selected index)
  | true =>
      simp only [↓reduceIte]
      change (_ + _) % modulus =
        ((sourceWord source index).val +
          (accumulatorWord source multiplier target selected index).val) % modulus
      rw [sourceWord_value source canonical index, Nat.add_comm]

/-- The literal selected modular multiply-accumulate output in the original target word. -/
def accumulatedWord (source multiplier target : Word) (selected : Bool) : Word :=
  if selected then
    ⟨(target.val + source.val * multiplier.val) % modulus,
      (Nat.mod_lt _ modulus_positive).trans modulus_lt_capacity⟩
  else target

lemma accumulatorWord_full (source multiplier target : Word) (selected : Bool)
    (canonical : Canonical target) :
    accumulatorWord source multiplier target selected width =
      accumulatedWord source multiplier target selected := by
  apply Fin.ext
  rw [accumulatedWord, conditional_value]
  have bound : (if selected then multiplier.val else 0) < 2 ^ width := by
    cases selected with
    | false => exact Nat.two_pow_pos width
    | true => exact multiplier.isLt
  have full := Nat.FixedWidth.ModularAccumulate.accumulateSelected_eq_add_mul_mod_of_lt_two_pow
    (N := modulus) (a := source.val) (x := if selected then multiplier.val else 0)
    (y := target.val) bound
  change Nat.FixedWidth.ModularAccumulate.accumulateSelected modulus source.val
    (if selected then multiplier.val else 0) target.val width = _
  exact full.trans (by cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt canonical])

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate
