/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Encoding
import all QuantumAlg.Util.Classical.Modular.Basic

/-!
# Original pure signed-coefficient reduction

The original widened operand width, two's-complement decoding, sign/magnitude
reduction and canonical residue theorems are independent of the old machine
interpreter. Their existing declaration names and bodies are preserved here.
No inverse correctness or runtime input assumption is added by this model.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction

open ClassicalAlgorithms ClassicalAlgorithms.NumberTheory ClassicalAlgorithms.Modular

/-- Width used by the shared XGCD call.  The extra bit is required for a
capacity modulus. -/
@[implicit_reducible]
def xgcdWidth (width : Nat) : Nat :=
  width + 1

/-- Width of the raw two's-complement coefficients produced by the widened
XGCD engine. -/
@[implicit_reducible]
def signedWidth (width : Nat) : Nat :=
  XGCD.PureXGCD.executionCoefficientWidth (xgcdWidth width)

theorem signedWidth_pos (width : Nat) : 0 < signedWidth width := by
  exact
    ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth_pos
      (xgcdWidth width)

/-- Canonical reduction of an arbitrary integer modulo a positive fixed-width
modulus. -/
def residueOfInt {width : Nat} (spec : ModulusSpec width) (value : Int) :
    Residue spec := by
  letI : NeZero spec.modulus :=
    ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  exact
    ⟨(value : ZMod spec.modulus).val,
      ZMod.val_lt (value : ZMod spec.modulus)⟩

/-- Interpret a raw widened-XGCD coefficient and reduce it to the unique
canonical residue. -/
def reduceRawCoefficient {width : Nat} (spec : ModulusSpec width)
    (raw : CShape.Word (signedWidth width)) : Residue spec :=
  residueOfInt spec
    (XGCD.decodeRawSignedWord (width := xgcdWidth width) raw)

/-- Whether an execution-width raw coefficient has its two's-complement sign
bit set. -/
def rawIsNegative {width : Nat}
    (raw : CShape.Word (signedWidth width)) : Bool :=
  decide (2 ^ (signedWidth width - 1) ≤ raw.toNat)

/-- Unsigned magnitude obtained by conditional two's-complement negation. -/
def rawMagnitude {width : Nat}
    (raw : CShape.Word (signedWidth width)) : Nat :=
  if rawIsNegative raw then
    CShape.wordModulus (signedWidth width) - raw.toNat
  else
    raw.toNat

/-- Remainder after reducing the unsigned coefficient magnitude. -/
def rawMagnitudeRemainder {width : Nat} (spec : ModulusSpec width)
    (raw : CShape.Word (signedWidth width)) : Nat :=
  rawMagnitude raw % spec.modulus

/-- Canonical natural value produced by the signed-reduction path.

A negative nonzero remainder `r` is corrected to `modulus - r`; a zero
remainder stays zero so a capacity modulus is never narrowed into `width`
bits. -/
def rawCanonicalNat {width : Nat} (spec : ModulusSpec width)
    (raw : CShape.Word (signedWidth width)) : Nat :=
  let remainder := rawMagnitudeRemainder spec raw
  if rawIsNegative raw then
    if remainder = 0 then 0 else spec.modulus - remainder
  else
    remainder

theorem rawCanonicalNat_lt_modulus {width : Nat}
    (spec : ModulusSpec width)
    (raw : CShape.Word (signedWidth width)) :
    rawCanonicalNat spec raw < spec.modulus := by
  have remainderLt :
      rawMagnitudeRemainder spec raw < spec.modulus :=
    Nat.mod_lt _ (modulusSpec_modulus_pos spec)
  by_cases negative : rawIsNegative raw = true
  · by_cases remainderZero : rawMagnitudeRemainder spec raw = 0
    · simp [rawCanonicalNat, negative, remainderZero,
        modulusSpec_modulus_pos spec]
    · simp only [rawCanonicalNat, negative, if_true, remainderZero,
        if_false]
      omega
  · have nonnegative : rawIsNegative raw = false :=
      Bool.eq_false_of_not_eq_true negative
    simpa [rawCanonicalNat, nonnegative] using remainderLt

/-- Intrinsic canonical residue computed by explicit signed-reduction
arithmetic. -/
def rawCanonicalResidue {width : Nat} (spec : ModulusSpec width)
    (raw : CShape.Word (signedWidth width)) : Residue spec :=
  ⟨rawCanonicalNat spec raw, rawCanonicalNat_lt_modulus spec raw⟩

@[simp] theorem rawCanonicalResidue_val {width : Nat}
    (spec : ModulusSpec width)
    (raw : CShape.Word (signedWidth width)) :
    (rawCanonicalResidue spec raw).val = rawCanonicalNat spec raw :=
  rfl

/-- The threshold test used by the machine path is the sign branch of the
two's-complement decoder. -/
theorem decodeRawSignedWord_eq_signedMagnitude {width : Nat}
    (raw : CShape.Word (signedWidth width)) :
    XGCD.decodeRawSignedWord (width := xgcdWidth width) raw =
      if rawIsNegative raw then
        -(rawMagnitude raw : Int)
      else
        (rawMagnitude raw : Int) := by
  change (BitVec.ofFin (decodeWord raw)).toInt = _
  rw [BitVec.toInt_eq_toNat_cond]
  have decodedValue : (decodeWord raw).val = raw.toNat := by
    cases raw
    rfl
  simp only [BitVec.toNat_ofFin, decodedValue]
  have widthPositive := signedWidth_pos width
  have powerSplit :
      2 ^ signedWidth width = 2 * 2 ^ (signedWidth width - 1) := by
    calc
      2 ^ signedWidth width =
          2 ^ (signedWidth width - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (signedWidth width - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (signedWidth width - 1) := Nat.mul_comm _ _
  by_cases negative : rawIsNegative raw = true
  · have threshold :
        2 ^ (signedWidth width - 1) ≤ raw.toNat := by
      unfold rawIsNegative at negative
      exact of_decide_eq_true negative
    have notSmall : ¬ 2 * raw.toNat < 2 ^ signedWidth width := by
      omega
    rw [if_neg notSmall]
    simp only [rawMagnitude, negative, if_true, CShape.wordModulus]
    have rawLe : raw.toNat ≤ 2 ^ signedWidth width :=
      Nat.le_of_lt raw.toNat_lt
    rw [Int.ofNat_sub rawLe]
    ring
  · have nonnegative : rawIsNegative raw = false :=
      Bool.eq_false_of_not_eq_true negative
    have notThreshold :
        ¬ 2 ^ (signedWidth width - 1) ≤ raw.toNat := by
      intro threshold
      apply negative
      unfold rawIsNegative
      exact decide_eq_true threshold
    have belowThreshold :
        raw.toNat < 2 ^ (signedWidth width - 1) := by
      exact Nat.lt_of_not_ge notThreshold
    have small : 2 * raw.toNat < 2 ^ signedWidth width := by
      omega
    rw [if_pos small]
    simp [rawMagnitude, nonnegative]

@[simp] theorem residueOfInt_natCast_val {width : Nat}
    (spec : ModulusSpec width) (value : Nat) :
    (residueOfInt spec (value : Int)).val = value % spec.modulus := by
  let _ : NeZero spec.modulus :=
    ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  change (((value : Int) : ZMod spec.modulus).val) = value % spec.modulus
  rw [Int.cast_natCast, ZMod.val_natCast]

@[simp] theorem residueOfInt_neg_natCast_val {width : Nat}
    (spec : ModulusSpec width) (value : Nat) :
    (residueOfInt spec (-(value : Int))).val =
      if value % spec.modulus = 0 then
        0
      else
        spec.modulus - value % spec.modulus := by
  let _ : NeZero spec.modulus :=
    ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  simp only [residueOfInt]
  rw [Int.cast_neg, Int.cast_natCast, ZMod.neg_val, ZMod.val_natCast]
  simp only [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

/-- The explicit sign/magnitude/remainder model is exactly the canonical
residue obtained from XGCD's public two's-complement decoder. -/
theorem rawCanonicalResidue_eq_reduceRawCoefficient {width : Nat}
    (spec : ModulusSpec width)
    (raw : CShape.Word (signedWidth width)) :
    rawCanonicalResidue spec raw = reduceRawCoefficient spec raw := by
  apply Fin.ext
  change rawCanonicalNat spec raw =
    (residueOfInt spec
      (XGCD.decodeRawSignedWord (width := xgcdWidth width) raw)).val
  rw [decodeRawSignedWord_eq_signedMagnitude]
  by_cases negative : rawIsNegative raw = true
  · simp [rawCanonicalNat, rawMagnitudeRemainder, negative]
    rfl
  · have nonnegative : rawIsNegative raw = false :=
      Bool.eq_false_of_not_eq_true negative
    simp [rawCanonicalNat, rawMagnitudeRemainder, nonnegative]

theorem residueOfInt_cast {width : Nat} (spec : ModulusSpec width)
    (value : Int) :
    ((residueOfInt spec value).val : ZMod spec.modulus) =
      (value : ZMod spec.modulus) := by
  let _ : NeZero spec.modulus :=
    ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  change ((value : ZMod spec.modulus).val : ZMod spec.modulus) =
    (value : ZMod spec.modulus)
  exact ZMod.natCast_zmod_val (value : ZMod spec.modulus)

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction
