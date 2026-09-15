/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Data.PNat.Defs
import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Log

/-!
# Closed classical storage shapes

`CShape` is the closed vocabulary from which proof-level classical storage is
derived.  Constructors carry only structural dimensions.  In particular, the
residue and elliptic-curve constructors describe canonical encodings; modulus,
curve, and value semantics belong to their later typed carriers rather than to
an arbitrary caller-supplied footprint.
-/

section

namespace QuantumAlg

/-- Closed shapes admitted by typed classical storage and instructions. -/
public inductive CShape where
  /-- No runtime bits. -/
  | unit
  /-- The canonical one-bit proof-level storage unit. -/
  | bit
  /-- One finite classical value; positivity provides an initial value. -/
  | finite (cardinality : ℕ+)
  /-- A fixed sequence of bits. -/
  | bits (count : Nat)
  /-- An unsigned fixed-width word. -/
  | unsignedWord (width : Nat)
  /-- A bounded signed fixed-width word. -/
  | boundedSignedWord (width : Nat)
  /-- A tag bit followed by storage reserved for the fixed payload encoding. -/
  | option (payload : CShape)
  /-- Adjacent encodings of two values. -/
  | product (left right : CShape)
  /-- A fixed-length vector of one fixed element shape. -/
  | fixedVector (length : Nat) (element : CShape)
  /-- A canonical residue encoded in the stated word width. -/
  | canonicalResidue (modulusWidth : Nat)
  /-- A proof-carrying unit residue; the proof is erased at runtime. -/
  | unitResidue (modulusWidth : Nat)
  /-- An infinity tag and two fixed-width affine coordinates. -/
  | ellipticCurvePoint (fieldWidth : Nat)
deriving DecidableEq

namespace CShape

/-- Exact proof-level storage width in bits. -/
@[expose]
public def bitWidth : CShape → Nat
  | .unit => 0
  | .bit => 1
  | .finite cardinality => Nat.clog 2 cardinality
  | .bits count => count
  | .unsignedWord width => width
  | .boundedSignedWord width => width
  | .option payload => 1 + payload.bitWidth
  | .product left right => left.bitWidth + right.bitWidth
  | .fixedVector length element => length * element.bitWidth
  | .canonicalResidue modulusWidth => modulusWidth
  | .unitResidue modulusWidth => modulusWidth
  | .ellipticCurvePoint fieldWidth => 1 + 2 * fieldWidth

@[simp] theorem bitWidth_unit : bitWidth .unit = 0 := rfl
@[simp] theorem bitWidth_bit : bitWidth .bit = 1 := rfl
@[simp] theorem bitWidth_finite (cardinality : ℕ+) :
    bitWidth (.finite cardinality) = Nat.clog 2 cardinality := rfl
@[simp] theorem bitWidth_bits (count : Nat) : bitWidth (.bits count) = count := rfl
@[simp] theorem bitWidth_unsignedWord (width : Nat) :
    bitWidth (.unsignedWord width) = width := rfl
@[simp] theorem bitWidth_boundedSignedWord (width : Nat) :
    bitWidth (.boundedSignedWord width) = width := rfl
@[simp] theorem bitWidth_option (payload : CShape) :
    bitWidth (.option payload) = 1 + payload.bitWidth := rfl
@[simp] theorem bitWidth_product (left right : CShape) :
    bitWidth (.product left right) = left.bitWidth + right.bitWidth := rfl
@[simp] theorem bitWidth_fixedVector (length : Nat) (element : CShape) :
    bitWidth (.fixedVector length element) = length * element.bitWidth := rfl
@[simp] theorem bitWidth_canonicalResidue (modulusWidth : Nat) :
    bitWidth (.canonicalResidue modulusWidth) = modulusWidth := rfl
@[simp] theorem bitWidth_unitResidue (modulusWidth : Nat) :
    bitWidth (.unitResidue modulusWidth) = modulusWidth := rfl
@[simp] theorem bitWidth_ellipticCurvePoint (fieldWidth : Nat) :
    bitWidth (.ellipticCurvePoint fieldWidth) = 1 + 2 * fieldWidth := rfl

/-- The binary storage width can encode every admitted finite value. -/
public theorem finite_capacity (cardinality : ℕ+) :
    (cardinality : Nat) ≤ 2 ^ bitWidth (.finite cardinality) :=
  Nat.le_pow_clog (by decide : 1 < (2 : Nat)) cardinality

/-- Canonical binary encoding of a finite classical value. Unused bit patterns
are not additional values of the classical register. -/
@[expose]
public def encodeFinite (cardinality : ℕ+) (value : Fin cardinality) :
    Fin (2 ^ bitWidth (.finite cardinality)) :=
  ⟨value.val, lt_of_lt_of_le value.isLt (finite_capacity cardinality)⟩

@[simp] theorem encodeFinite_val (cardinality : ℕ+) (value : Fin cardinality) :
    (encodeFinite cardinality value).val = value.val := rfl

/-- Binary encoding preserves distinct finite classical outcomes. -/
public theorem encodeFinite_injective (cardinality : ℕ+) :
    Function.Injective (encodeFinite cardinality) := by
  intro left right equal
  apply Fin.ext
  exact congrArg
    (fun value : Fin (2 ^ bitWidth (.finite cardinality)) => value.val) equal

/-- Decode a binary encoding only when it names a value in the finite domain. -/
@[expose]
public def decodeFinite (cardinality : ℕ+)
    (encoding : Fin (2 ^ bitWidth (.finite cardinality))) :
    Option (Fin cardinality) :=
  if valid : encoding.val < cardinality then some ⟨encoding.val, valid⟩ else none

@[simp] theorem decodeFinite_encodeFinite (cardinality : ℕ+) (value : Fin cardinality) :
    decodeFinite cardinality (encodeFinite cardinality value) = some value := by
  simp [decodeFinite, encodeFinite, value.isLt]

/-- Unused binary patterns are rejected rather than reduced modulo the domain. -/
theorem decodeFinite_eq_none (cardinality : ℕ+)
    (encoding : Fin (2 ^ bitWidth (.finite cardinality)))
    (invalid : (cardinality : Nat) ≤ encoding.val) :
    decodeFinite cardinality encoding = none := by
  simp [decodeFinite, Nat.not_lt.mpr invalid]

/-- Every injective fixed-width binary encoding needs at least the canonical
ceiling-logarithm width. This is a classical storage statement. -/
public theorem finite_bitWidth_minimal (cardinality : ℕ+) (width : Nat)
    (encoding : Fin cardinality → Fin (2 ^ width))
    (injective : Function.Injective encoding) :
    bitWidth (.finite cardinality) ≤ width := by
  change Nat.clog 2 (cardinality : Nat) ≤ width
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : Nat))).2
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective encoding injective

end CShape

namespace AccountingShapeFixtures

/-- Every classical storage magnitude is derived from a closed shape. -/
example : CShape.bitWidth (.fixedVector 3 (.option (.unsignedWord 8))) = 27 := by
  decide

/-- Proof fields in unit residues do not add runtime storage. -/
example : CShape.bitWidth (.unitResidue 255) = 255 := rfl

/-- The point encoding has one infinity tag and two coordinates. -/
example : CShape.bitWidth (.ellipticCurvePoint 256) = 513 := by decide

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check CShape.opaque

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check CShape.claimedBits

end AccountingShapeFixtures

end QuantumAlg

end
