/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import all QuantumAlg.Util.Classical.Arithmetic
import all QuantumAlg.Util.Classical.Modular.Additive

/-!
# Shared fixed-width number-theory representations

This module fixes the semantic interpretation of the nominal
`boundedSignedWord` shape used by fixed-width number-theory routines.  The
runtime representation is exactly one `Fin (2 ^ width)`, while `BitVec.toInt`
provides its two's-complement interpretation.

It also defines public, width-derived bounds used by Euclidean and extended
Euclidean routines.  The XGCD coefficient width is derived from the maximum
Mathlib coefficient magnitude over the finite pair of input-word domains.  It
is therefore uniform in the public width without asserting an unproved closed
formula for `Nat.gcdA` or `Nat.gcdB`.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace NumberTheory

/-! ## Two's-complement signed words -/

/-- A bounded signed value backed by exactly one raw `width`-bit vector.

The wrapper is intentionally representation-transparent through `encode` and
`decode`: Core's nominal `.boundedSignedWord width` stores the same
`Fin (2 ^ width)` and assigns it no competing signed semantics. -/
structure BoundedSigned (width : Nat) where
  /-- The bits whose two's-complement interpretation is the semantic value. -/
  bits : BitVec width
deriving DecidableEq

namespace BoundedSigned

/-- Interpret a bounded signed word as a two's-complement integer. -/
def toInt {width : Nat} (value : BoundedSigned width) : Int :=
  value.bits.toInt

/-- Expose the raw encoding stored by Core's nominal bounded-signed shape. -/
def encode {width : Nat} (value : BoundedSigned width) : Word width :=
  value.bits.toFin

/-- Give a raw fixed-width word its unique two's-complement interpretation. -/
def decode {width : Nat} (encoding : Word width) : BoundedSigned width :=
  ⟨BitVec.ofFin encoding⟩

/-- Encode an integer modulo the word modulus using two's complement. -/
def ofInt (width : Nat) (value : Int) : BoundedSigned width :=
  ⟨BitVec.ofInt width value⟩

@[ext] lemma ext {width : Nat} {left right : BoundedSigned width}
    (bits : left.bits = right.bits) : left = right := by
  cases left
  cases right
  cases bits
  rfl

/-- Decoding and re-encoding preserves every raw word, including width zero. -/
@[simp] lemma encode_decode {width : Nat} (encoding : Word width) :
    encode (decode encoding) = encoding := by
  rfl

/-- Encoding and decoding preserves every bounded signed value. -/
@[simp] lemma decode_encode {width : Nat} (value : BoundedSigned width) :
    decode (encode value) = value := by
  apply ext
  exact BitVec.ofFin_toFin value.bits

/-- The raw natural payload of the signed encoding is unchanged. -/
@[simp] lemma encode_val {width : Nat} (value : BoundedSigned width) :
    value.encode.val = value.bits.toNat :=
  rfl

/-- Decoding a Core-compatible raw word uses `BitVec`'s two's-complement
interpretation. -/
@[simp] lemma toInt_decode {width : Nat} (encoding : Word width) :
    (decode encoding).toInt = Int.bmod encoding.val (2 ^ width) := by
  simp [decode, toInt]

/-- Integer construction stores the ordinary fixed-width modular encoding. -/
lemma encode_ofInt_val (width : Nat) (value : Int) :
    (BitVec.ofInt width value).toNat =
      (value % (2 ^ width : Int)).toNat := by
  simp

/-- Reading an integer construction gives its balanced modular representative. -/
@[simp] lemma toInt_ofInt (width : Nat) (value : Int) :
    (ofInt width value).toInt = value.bmod (2 ^ width) := by
  change (BitVec.ofInt width value).toInt = value.bmod (2 ^ width)
  exact BitVec.toInt_ofInt (n := width) value

/-- Re-encoding the represented integer preserves the exact signed word. -/
@[simp] lemma ofInt_toInt {width : Nat} (value : BoundedSigned width) :
    ofInt width value.toInt = value := by
  apply ext
  exact BitVec.ofInt_toInt

/-- Every signed word satisfies the lower two's-complement boundary. -/
lemma lowerBound {width : Nat} (value : BoundedSigned width) :
    -(2 ^ (width - 1) : Int) ≤ value.toInt := by
  exact BitVec.le_toInt value.bits

/-- Every signed word satisfies the strict upper two's-complement boundary. -/
lemma upperBound {width : Nat} (value : BoundedSigned width) :
    value.toInt < (2 ^ (width - 1) : Int) := by
  exact BitVec.toInt_lt

/-- An integer already in the nonempty-width signed range survives encoding
without wraparound. -/
lemma toInt_ofInt_eq_self {width : Nat} (widthPositive : 0 < width)
    {value : Int} (lower : -(2 ^ (width - 1) : Int) ≤ value)
    (upper : value < (2 ^ (width - 1) : Int)) :
    (ofInt width value).toInt = value := by
  exact BitVec.toInt_ofInt_eq_self widthPositive lower upper

end BoundedSigned

/-! ## Uniform Euclidean and XGCD widths -/

/-- A conservative fixed iteration budget for Euclid on two equal-width
words.  Any active remainder is below this value and strictly decreases. -/
def euclidFuel (width : Nat) : Nat :=
  modulus width

@[simp] lemma euclidFuel_eq_two_pow (width : Nat) :
    euclidFuel width = 2 ^ width :=
  rfl

lemma euclidFuel_pos (width : Nat) : 0 < euclidFuel width := by
  exact fixedWidthModulus_pos width

lemma word_val_lt_euclidFuel {width : Nat} (word : Word width) :
    word.val < euclidFuel width := by
  exact fixedWidthWord_lt_modulus word

/-- The larger magnitude of Mathlib's selected Bezout coefficients for one
fixed-width input pair. -/
def xgcdCoefficientMagnitude {width : Nat}
    (left right : Word width) : Nat :=
  max (Nat.gcdA left.val right.val).natAbs
    (Nat.gcdB left.val right.val).natAbs

/-- The maximum selected Bezout-coefficient magnitude over all pairs of words
of one public width. -/
def xgcdCoefficientBound (width : Nat) : Nat :=
  Finset.univ.sup fun input : Word width × Word width =>
    xgcdCoefficientMagnitude input.1 input.2

/-- A uniform signed width with one guard bit beyond the finite-domain
coefficient magnitude. -/
public def coefficientWidth (width : Nat) : Nat :=
  Nat.size (xgcdCoefficientBound width) + 2

lemma coefficientWidth_pos (width : Nat) : 0 < coefficientWidth width := by
  simp [coefficientWidth]

/-- The finite-domain maximum bounds the first selected Bezout coefficient. -/
lemma gcdA_natAbs_le_xgcdCoefficientBound {width : Nat}
    (left right : Word width) :
    (Nat.gcdA left.val right.val).natAbs ≤
      xgcdCoefficientBound width := by
  calc
    (Nat.gcdA left.val right.val).natAbs ≤
        xgcdCoefficientMagnitude left right :=
      Nat.le_max_left _ _
    _ ≤ xgcdCoefficientBound width := by
      unfold xgcdCoefficientBound
      exact Finset.le_sup
        (s := (Finset.univ : Finset (Word width × Word width)))
        (f := fun input : Word width × Word width =>
          xgcdCoefficientMagnitude input.1 input.2)
        (Finset.mem_univ (left, right))

/-- The finite-domain maximum bounds the second selected Bezout coefficient. -/
lemma gcdB_natAbs_le_xgcdCoefficientBound {width : Nat}
    (left right : Word width) :
    (Nat.gcdB left.val right.val).natAbs ≤
      xgcdCoefficientBound width := by
  calc
    (Nat.gcdB left.val right.val).natAbs ≤
        xgcdCoefficientMagnitude left right :=
      Nat.le_max_right _ _
    _ ≤ xgcdCoefficientBound width := by
      unfold xgcdCoefficientBound
      exact Finset.le_sup
        (s := (Finset.univ : Finset (Word width × Word width)))
        (f := fun input : Word width × Word width =>
          xgcdCoefficientMagnitude input.1 input.2)
        (Finset.mem_univ (left, right))

/-- The public coefficient width has strictly more positive signed capacity
than the maximum selected coefficient magnitude. -/
lemma xgcdCoefficientBound_lt_signedCapacity (width : Nat) :
    xgcdCoefficientBound width <
      2 ^ (coefficientWidth width - 1) := by
  have bound_lt_size :
      xgcdCoefficientBound width <
        2 ^ Nat.size (xgcdCoefficientBound width) :=
    Nat.lt_size_self _
  have size_capacity_le :
      2 ^ Nat.size (xgcdCoefficientBound width) ≤
        2 ^ (Nat.size (xgcdCoefficientBound width) + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  simpa [coefficientWidth] using bound_lt_size.trans_le size_capacity_le

/-- Any integer below the finite XGCD magnitude bound lies in the public
two's-complement coefficient range. -/
lemma int_in_coefficientRange_of_natAbs_le {width : Nat} {value : Int}
    (magnitude : value.natAbs ≤ xgcdCoefficientBound width) :
    -(2 ^ (coefficientWidth width - 1) : Int) ≤ value ∧
      value < (2 ^ (coefficientWidth width - 1) : Int) := by
  have capacity := xgcdCoefficientBound_lt_signedCapacity width
  have magnitude_lt : value.natAbs <
      2 ^ (coefficientWidth width - 1) :=
    magnitude.trans_lt capacity
  have upperNat : (value.natAbs : Int) <
      (2 ^ (coefficientWidth width - 1) : Nat) :=
    Int.ofNat_lt.mpr magnitude_lt
  have capacityCast :
      ((2 ^ (coefficientWidth width - 1) : Nat) : Int) =
        (2 ^ (coefficientWidth width - 1) : Int) := by
    norm_num
  rw [← capacityCast]
  by_cases nonnegative : 0 ≤ value
  · have absEq : (value.natAbs : Int) = value :=
      Int.natAbs_of_nonneg nonnegative
    rw [absEq] at upperNat
    constructor
    · have capacityNonnegative :
          (0 : Int) ≤ (2 ^ (coefficientWidth width - 1) : Nat) := by
        positivity
      omega
    · exact upperNat
  · have nonpositive : value ≤ 0 := Int.le_of_not_le nonnegative
    have absEq : (value.natAbs : Int) = -value :=
      Int.ofNat_natAbs_of_nonpos nonpositive
    rw [absEq] at upperNat
    constructor
    · omega
    · have capacityPositive :
          (0 : Int) < (2 ^ (coefficientWidth width - 1) : Nat) := by
        positivity
      omega

/-- Every first Mathlib XGCD coefficient for same-width words is represented
exactly at `coefficientWidth`. -/
lemma gcdA_toInt_ofInt_coefficientWidth {width : Nat}
    (left right : Word width) :
    (BoundedSigned.ofInt (coefficientWidth width)
        (Nat.gcdA left.val right.val)).toInt =
      Nat.gcdA left.val right.val := by
  rcases int_in_coefficientRange_of_natAbs_le
      (gcdA_natAbs_le_xgcdCoefficientBound left right) with
    ⟨lower, upper⟩
  exact BoundedSigned.toInt_ofInt_eq_self
    (coefficientWidth_pos width) lower upper

/-- Every second Mathlib XGCD coefficient for same-width words is represented
exactly at `coefficientWidth`. -/
lemma gcdB_toInt_ofInt_coefficientWidth {width : Nat}
    (left right : Word width) :
    (BoundedSigned.ofInt (coefficientWidth width)
        (Nat.gcdB left.val right.val)).toInt =
      Nat.gcdB left.val right.val := by
  rcases int_in_coefficientRange_of_natAbs_le
      (gcdB_natAbs_le_xgcdCoefficientBound left right) with
    ⟨lower, upper⟩
  exact BoundedSigned.toInt_ofInt_eq_self
    (coefficientWidth_pos width) lower upper

end NumberTheory

end ClassicalAlgorithms
end QuantumAlg

end
