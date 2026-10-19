/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
import QuantumAlg.Init
public import QuantumAlg.Core.Base.Accounting.Shape
public import QuantumAlg.Core.Base.Classical.Value
import all QuantumAlg.Core.Base.Classical.Value
public import Mathlib.Data.Fintype.Card
import all QuantumAlg.Core.Base.Accounting.Flow
import Mathlib.Data.Nat.Bitwise

/-!
# Closed shape-indexed classical instructions

`ClassicalOp input output pre post` describes the closed bit/word operations
used by the built-in classical model. Its constructors fix operand and result
shapes, preserve one exact live context, and determine value semantics and
physical storage flow. Executable admission and event accounting belong to
the selected model token placed in the circuit.

The family intentionally contains only reusable bit, fixed-width word,
fixed-vector, and narrow nominal-encoding operations.  The latter can only
materialize or erase a statically prescribed storage representation; they do
not interpret signed values, validate residues, or recover semantic data.
The built-in model also declares uniform random bits. Allocation and lexical
workspace remain structural circuit instructions. Modular, elliptic-curve, and
recovery algorithms must be expanded
into their actual instructions.
-/

section

namespace QuantumAlg

namespace CShape

namespace Value

/-- Boolean stored by one nominal bit value. -/
public def toBool : Value .bit → Bool
  | .bit value => value

/-- The actual finite-domain value of a classical register. -/
@[expose]
public def toFin {cardinality : ℕ+} : Value (.finite cardinality) → Fin cardinality
  | .finite value => value

@[simp] lemma toFin_finite {cardinality : ℕ+} (value : Fin cardinality) :
    (Value.finite value).toFin = value := rfl

/-- Natural encoding stored by one nominal unsigned word. -/
public def toNat {width : Nat} : Value (.unsignedWord width) → Nat
  | .unsignedWord value => value.val

/-- The stored unsigned-word encoding is within its declared width. -/
lemma toNat_lt {width : Nat} (value : Value (.unsignedWord width)) :
    value.toNat < 2 ^ width := by
  cases value with
  | unsignedWord value => exact value.isLt

/-- Raw finite encoding stored by one nominal canonical-residue value.

This projection carries no modulus or canonicality claim beyond the declared
storage width. -/
def residueEncoding {width : Nat} :
    Value (.canonicalResidue width) → Fin (2 ^ width)
  | .canonicalResidue encoding => encoding

/-- Raw finite encoding stored by one nominal bounded-signed value.

This projection assigns no signed interpretation to the stored bits. -/
def boundedSignedEncoding {width : Nat} :
    Value (.boundedSignedWord width) → Fin (2 ^ width)
  | .boundedSignedWord encoding => encoding

/-- Raw finite encoding stored by one proof-carrying unit-residue value.

The erased proof and modulus semantics belong to the later semantic carrier. -/
def unitResidueEncoding {width : Nat} :
    Value (.unitResidue width) → Fin (2 ^ width)
  | .unitResidue encoding => encoding

/-- First component of a nominal product value. -/
public def first {left right : CShape} : Value (.product left right) → Value left
  | .product first _second => first

/-- Second component of a nominal product value. -/
public def second {left right : CShape} : Value (.product left right) → Value right
  | .product _first second => second

/-- Read one statically valid position of a nominal fixed vector. -/
public def get {length : Nat} {element : CShape} :
    Value (.fixedVector length element) → Fin length → Value element
  | .fixedVector values, index => values index

/-- Read one statically valid position of a nominal fixed bit vector. -/
public def bitGet {count : Nat} :
    Value (.bits count) → Fin count → Value .bit
  | .bits values, index => .bit (values index)

/-- Read one statically valid most-significant-bit-first position of a
nominal unsigned word. -/
public def wordBitGet {width : Nat} :
    Value (.unsignedWord width) → Fin width → Value .bit
  | .unsignedWord value, index =>
      .bit (value.val.testBit (width - 1 - index.val))

end Value

/-- The runtime encoding of one unsigned fixed-width word. -/
public abbrev Word (width : Nat) := Value (.unsignedWord width)

/-- The positive modulus represented by one fixed word width. -/
@[expose] public def wordModulus (width : Nat) : Nat :=
  2 ^ width

public lemma wordModulus_pos (width : Nat) : 0 < wordModulus width := by
  exact Nat.two_pow_pos width

/-- Canonically truncate a natural number to one fixed-width word. -/
@[expose] public def wordOfNat (width value : Nat) : Word width :=
  .unsignedWord
    ⟨value % wordModulus width, Nat.mod_lt value (wordModulus_pos width)⟩

@[simp] lemma wordOfNat_val (width value : Nat) :
    (wordOfNat width value).toNat = value % wordModulus width :=
  rfl

/-- Deterministic raw initialization for one nominal storage shape.

This initializes an encoding only.  In particular, zero-valued unit residues
and affine coordinates carry no modulus, unit, curve, or validity claim. -/
public def initialValue : (shape : CShape) → Value shape
  | .unit => .unit
  | .bit => .bit false
  | .finite cardinality => .finite ⟨0, cardinality.pos⟩
  | .bits _count => .bits fun _index => false
  | .unsignedWord width => wordOfNat width 0
  | .boundedSignedWord width =>
      .boundedSignedWord ⟨0, Nat.two_pow_pos width⟩
  | .option _payload => .optionNone
  | .product left right => .product (initialValue left) (initialValue right)
  | .fixedVector _length element => .fixedVector fun _index => initialValue element
  | .canonicalResidue modulusWidth =>
      .canonicalResidue ⟨0, Nat.two_pow_pos modulusWidth⟩
  | .unitResidue modulusWidth =>
      .unitResidue ⟨0, Nat.two_pow_pos modulusWidth⟩
  | .ellipticCurvePoint fieldWidth =>
      .ellipticCurvePoint true
        ⟨0, Nat.two_pow_pos fieldWidth⟩ ⟨0, Nat.two_pow_pos fieldWidth⟩

@[simp] lemma initialValue_bit : initialValue .bit = .bit false := rfl

@[simp] lemma initialValue_finite (cardinality : ℕ+) :
    initialValue (.finite cardinality) = .finite ⟨0, cardinality.pos⟩ := rfl

@[simp] lemma initialValue_bits (width : Nat) :
    initialValue (.bits width) = .bits fun _index => false := rfl

@[simp] lemma initialValue_unsignedWord (width : Nat) :
    initialValue (.unsignedWord width) = wordOfNat width 0 := rfl

/-- Resize one unsigned word with truncation modulo the target word modulus. -/
def wordResize {sourceWidth : Nat} (targetWidth : Nat)
    (input : Word sourceWidth) : Word targetWidth :=
  wordOfNat targetWidth input.toNat

/-! ## Sealed nominal encoding adapters -/

/-- Materialize binary measurement-register values in their existing order.
The two possible finite encodings become the corresponding Boolean bits. -/
def packFiniteBits (count : Nat)
    (input : Value (.fixedVector count (.finite 2))) : Value (.bits count) :=
  .bits fun index => decide ((input.get index).toFin.val = 1)

/-- Materialize a nominal product without flattening or reordering it. -/
def packProduct {left right : CShape}
    (input : Value (.product left right)) : Value (.product left right) :=
  input

/-- Store an unsigned word unchanged in the distinct bounded-signed shape.

This operation is a raw nominal cast only.  In particular, it does not
negate, sign-extend, normalize, or interpret the encoding as an integer. -/
def packBoundedSignedWord (width : Nat)
    (input : Word width) : Value (.boundedSignedWord width) :=
  match input with
  | .unsignedWord encoding => .boundedSignedWord encoding

/-- Materialize a tag and payload as an optional value.

`false` selects `none`; `true` retains the supplied payload as `some`. -/
def packOption {payload : CShape}
    (input : Value (.product .bit payload)) : Value (.option payload) :=
  match input with
  | .product (.bit false) _value => .optionNone
  | .product (.bit true) value => .optionSome value

/-- Expose an optional encoding as a tag and payload.

An absent payload is normalized to the deterministic initial encoding. -/
def unpackOption {payload : CShape}
    (input : Value (.option payload)) : Value (.product .bit payload) :=
  match input with
  | .optionNone => .product (.bit false) (initialValue payload)
  | .optionSome value => .product (.bit true) value

/-- Erase the unit-residue wrapper while preserving the exact raw word.

This representation operation neither checks nor manufactures a unit proof. -/
def unpackUnitResidue (width : Nat)
    (input : Value (.unitResidue width)) : Word width :=
  match input with
  | .unitResidue encoding => .unsignedWord encoding

/-- Product materialization preserves both components and their nesting. -/
lemma packProduct_eq {left right : CShape}
    (input : Value (.product left right)) : packProduct input = input :=
  rfl

/-- Bounded-signed packing preserves the exact raw finite encoding. -/
lemma packBoundedSignedWord_encoding (width : Nat) (input : Word width) :
    (packBoundedSignedWord width input).boundedSignedEncoding.val = input.toNat := by
  cases input
  rfl

/-- A false tag materializes the empty optional encoding. -/
lemma packOption_false {payload : CShape} (value : Value payload) :
    packOption (.product (.bit false) value) = .optionNone :=
  rfl

/-- A true tag materializes the supplied payload. -/
lemma packOption_true {payload : CShape} (value : Value payload) :
    packOption (.product (.bit true) value) = .optionSome value :=
  rfl

/-- An empty optional encoding exposes a false tag and initialized payload. -/
lemma unpackOption_none {payload : CShape} :
    unpackOption (.optionNone : Value (.option payload)) =
      .product (.bit false) (initialValue payload) :=
  rfl

/-- A present optional encoding exposes its true tag and exact payload. -/
lemma unpackOption_some {payload : CShape} (value : Value payload) :
    unpackOption (.optionSome value) = .product (.bit true) value :=
  rfl

/-- Packing an unpacked optional encoding returns its exact original value. -/
lemma packOption_unpackOption {payload : CShape} (input : Value (.option payload)) :
    packOption (unpackOption input) = input := by
  cases input <;> rfl

/-- Unpacking a false-tagged packed value normalizes its unused payload. -/
lemma unpackOption_packOption_false {payload : CShape} (value : Value payload) :
    unpackOption (packOption (.product (.bit false) value)) =
      .product (.bit false) (initialValue payload) :=
  rfl

/-- Unpacking a true-tagged packed value preserves its exact payload. -/
lemma unpackOption_packOption_true {payload : CShape} (value : Value payload) :
    unpackOption (packOption (.product (.bit true) value)) =
      .product (.bit true) value :=
  rfl

/-- Unit-residue unpacking preserves the exact raw finite encoding. -/
lemma unpackUnitResidue_toNat (width : Nat)
    (input : Value (.unitResidue width)) :
    (unpackUnitResidue width input).toNat = input.unitResidueEncoding.val := by
  cases input
  rfl

/-- Read a raw nominal residue encoding as an equal-width unsigned word. -/
def unpackCanonicalResidue (width : Nat)
    (input : Value (.canonicalResidue width)) : Word width :=
  match input with
  | .canonicalResidue encoding => .unsignedWord encoding

/-- Store an unsigned word as an equal-width raw nominal residue encoding.

This representation operation does not establish validity for any modulus. -/
def packCanonicalResidue (width : Nat)
    (input : Word width) : Value (.canonicalResidue width) :=
  match input with
  | .unsignedWord encoding => .canonicalResidue encoding

namespace Value

/-- Read the raw infinity tag stored by an elliptic-curve point encoding.

This projection assigns no curve, field, or validity semantics to the tag. -/
def ellipticCurvePointInfinityTag {width : Nat} :
    Value (.ellipticCurvePoint width) → Bool
  | .ellipticCurvePoint infinityTag _x _y => infinityTag

/-- Read the raw `x` coordinate stored by an elliptic-curve point encoding.

This projection assigns no field or canonicality semantics to the coordinate. -/
def ellipticCurvePointX {width : Nat} :
    Value (.ellipticCurvePoint width) → Fin (2 ^ width)
  | .ellipticCurvePoint _infinityTag x _y => x

/-- Read the raw `y` coordinate stored by an elliptic-curve point encoding.

This projection assigns no field or canonicality semantics to the coordinate. -/
def ellipticCurvePointY {width : Nat} :
    Value (.ellipticCurvePoint width) → Fin (2 ^ width)
  | .ellipticCurvePoint _infinityTag _x y => y

end Value

/-- Expose one raw elliptic-curve point as its tag and two fixed-width words.

This representation operation neither validates the point nor interprets the
tag or coordinates. -/
def unpackEllipticCurvePoint (width : Nat)
    (input : Value (.ellipticCurvePoint width)) :
    Value (.product .bit
      (.product (.unsignedWord width) (.unsignedWord width))) :=
  match input with
  | .ellipticCurvePoint infinityTag x y =>
      .product (.bit infinityTag)
        (.product (.unsignedWord x) (.unsignedWord y))

/-- Materialize a raw elliptic-curve point from its tag and two fixed-width words.

This representation operation neither validates the point nor interprets the
tag or coordinates. -/
def packEllipticCurvePoint (width : Nat)
    (input : Value (.product .bit
      (.product (.unsignedWord width) (.unsignedWord width)))) :
    Value (.ellipticCurvePoint width) :=
  match input with
  | .product (.bit infinityTag) (.product (.unsignedWord x) (.unsignedWord y)) =>
      .ellipticCurvePoint infinityTag x y

@[simp] lemma unpackEllipticCurvePoint_infinityTag (width : Nat)
    (input : Value (.ellipticCurvePoint width)) :
    (unpackEllipticCurvePoint width input).first.toBool =
      input.ellipticCurvePointInfinityTag := by
  cases input
  rfl

@[simp] lemma unpackEllipticCurvePoint_x (width : Nat)
    (input : Value (.ellipticCurvePoint width)) :
    (unpackEllipticCurvePoint width input).second.first.toNat =
      input.ellipticCurvePointX.val := by
  cases input
  rfl

@[simp] lemma unpackEllipticCurvePoint_y (width : Nat)
    (input : Value (.ellipticCurvePoint width)) :
    (unpackEllipticCurvePoint width input).second.second.toNat =
      input.ellipticCurvePointY.val := by
  cases input
  rfl

@[simp] lemma unpackEllipticCurvePoint_packEllipticCurvePoint (width : Nat)
    (input : Value (.product .bit
      (.product (.unsignedWord width) (.unsignedWord width)))) :
    unpackEllipticCurvePoint width (packEllipticCurvePoint width input) = input := by
  cases input with
  | product tag coordinates =>
      cases tag
      cases coordinates with
      | product x y =>
          cases x
          cases y
          rfl

@[simp] lemma packEllipticCurvePoint_unpackEllipticCurvePoint (width : Nat)
    (input : Value (.ellipticCurvePoint width)) :
    packEllipticCurvePoint width (unpackEllipticCurvePoint width input) = input := by
  cases input
  rfl

@[simp] lemma unpackCanonicalResidue_packCanonicalResidue
    (width : Nat) (input : Word width) :
    unpackCanonicalResidue width (packCanonicalResidue width input) = input := by
  cases input
  rfl

@[simp] lemma packCanonicalResidue_unpackCanonicalResidue
    (width : Nat) (input : Value (.canonicalResidue width)) :
    packCanonicalResidue width (unpackCanonicalResidue width input) = input := by
  cases input
  rfl

/-- One-bit-left shift with fixed-width truncation. -/
def wordShiftLeft (width : Nat) (input : Word width) : Word width :=
  wordOfNat width (2 * input.toNat)

/-- One-bit logical-right shift. -/
def wordShiftRight (width : Nat) (input : Word width) : Word width :=
  wordOfNat width (input.toNat / 2)

/-- Bitwise complement inside the declared word width. -/
def wordComplement (width : Nat) (input : Word width) : Word width :=
  wordOfNat width (wordModulus width - 1 - input.toNat)

/-- Fixed-width wrapping subtraction on unsigned words. -/
def wordSub (width : Nat) (left right : Word width) : Word width :=
  wordOfNat width (left.toNat + wordModulus width - right.toNat)

/-- Bitwise conjunction on the represented fixed-width bits. -/
def wordBitAnd (width : Nat) (left right : Word width) : Word width :=
  wordOfNat width (left.toNat &&& right.toNat)

/-- Bitwise disjunction on the represented fixed-width bits. -/
def wordBitOr (width : Nat) (left right : Word width) : Word width :=
  wordOfNat width (left.toNat ||| right.toNat)

/-- Bitwise exclusive-or on the represented fixed-width bits. -/
def wordBitXor (width : Nat) (left right : Word width) : Word width :=
  wordOfNat width (left.toNat ^^^ right.toNat)

/-- Pure fixed-width add-with-carry semantics used by the instruction layer. -/
def addCarry (width : Nat)
    (input : Value (.product (.unsignedWord width) (.unsignedWord width))) :
    Value (.product (.unsignedWord width) .bit) :=
  match input with
  | .product left right =>
      let sum := left.toNat + right.toNat
      .product (wordOfNat width sum) (.bit (decide (wordModulus width ≤ sum)))

/-- Pure fixed-width subtract-with-borrow semantics used by the instruction layer. -/
def subBorrow (width : Nat)
    (input : Value (.product (.unsignedWord width) (.unsignedWord width))) :
    Value (.product (.unsignedWord width) .bit) :=
  match input with
  | .product left right =>
      .product (wordSub width left right) (.bit (decide (left.toNat < right.toNat)))

/-- Pure full-width multiplication semantics used by the instruction layer. -/
def mulFull (leftWidth rightWidth : Nat)
    (input : Value
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth))) :
    Value (.unsignedWord (leftWidth + rightWidth)) :=
  match input with
  | .product left right =>
      wordOfNat (leftWidth + rightWidth) (left.toNat * right.toNat)

/-- Total machine semantics for quotient and remainder.

This closed instruction is deliberately total because `eval` is an interpreter,
but the public `DivRem` problem admits only nonzero divisors and uses the valid-
input theorems below.  Lean's division-by-zero value is therefore not a public
algorithm result. -/
def divRem (numeratorWidth divisorWidth : Nat)
    (input : Value
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))) :
    Value
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)) :=
  match input with
  | .product numerator divisor =>
      .product (wordOfNat numeratorWidth (numerator.toNat / divisor.toNat))
        (wordOfNat divisorWidth (numerator.toNat % divisor.toNat))

/-- Pure fixed-vector update semantics used by the instruction layer. -/
def vectorWrite {length : Nat} {element : CShape}
    (values : Value (.fixedVector length element)) (index : Fin length)
    (newValue : Value element) : Value (.fixedVector length element) :=
  .fixedVector (Function.update values.get index newValue)

/-- Swap two statically valid positions of a fixed vector. -/
def vectorSwap {length : Nat} {element : CShape}
    (values : Value (.fixedVector length element))
    (left right : Fin length) : Value (.fixedVector length element) :=
  .fixedVector
    (Function.update
      (Function.update values.get left (values.get right))
      right (values.get left))

/-- Xor one fixed-width row into another statically valid row. -/
def vectorRowXor {length width : Nat}
    (values : Value (.fixedVector length (.unsignedWord width)))
    (source destination : Fin length) :
    Value (.fixedVector length (.unsignedWord width)) :=
  .fixedVector
    (Function.update values.get destination
      (wordBitXor width (values.get destination) (values.get source)))

end CShape

/-- A classical register whose values form one prescribed nonempty finite
domain. Its binary storage is fixed by the corresponding closed shape. -/
public abbrev ClassicalRegister (cardinality : ℕ+) :=
  CShape.Value (.finite cardinality)

namespace ClassicalRegister

/-- The nominal classical register has exactly its declared finite value domain. -/
@[expose]
public def finEquiv (cardinality : ℕ+) : ClassicalRegister cardinality ≃ Fin cardinality where
  toFun := CShape.Value.toFin
  invFun := CShape.Value.finite
  left_inv := by
    intro value
    cases value
    rfl
  right_inv := fun _value => rfl

public instance (cardinality : ℕ+) : Fintype (ClassicalRegister cardinality) :=
  Fintype.ofEquiv (Fin cardinality) (finEquiv cardinality).symm

public instance (cardinality : ℕ+) : DecidableEq (ClassicalRegister cardinality) :=
  (finEquiv cardinality).decidableEq

public instance (cardinality : ℕ+) : Inhabited (ClassicalRegister cardinality) :=
  ⟨.finite ⟨0, cardinality.pos⟩⟩

/-- Finite-register cardinality counts values, including no unused bit patterns. -/
@[simp] public lemma card (cardinality : ℕ+) :
    Fintype.card (ClassicalRegister cardinality) = (cardinality : Nat) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (finEquiv cardinality)

/-- Store the actual finite-domain label in the canonical binary representation. -/
@[expose]
public def encode {cardinality : ℕ+} (value : ClassicalRegister cardinality) :
    Fin (2 ^ CShape.bitWidth (.finite cardinality)) :=
  CShape.encodeFinite cardinality value.toFin

/-- No two finite classical values share their binary storage representation. -/
public lemma encode_injective (cardinality : ℕ+) :
    Function.Injective (encode (cardinality := cardinality)) := by
  intro left right equal
  apply (finEquiv cardinality).injective
  exact CShape.encodeFinite_injective cardinality equal

/-- Decode binary storage while rejecting unused encodings. -/
@[expose]
public def decode (cardinality : ℕ+)
    (encoding : Fin (2 ^ CShape.bitWidth (.finite cardinality))) :
    Option (ClassicalRegister cardinality) :=
  (CShape.decodeFinite cardinality encoding).map CShape.Value.finite

@[simp] public lemma decode_encode {cardinality : ℕ+}
    (value : ClassicalRegister cardinality) :
    decode cardinality (encode value) = some value := by
  cases value with
  | finite value =>
      simp [decode, encode, CShape.decodeFinite_encodeFinite, CShape.Value.toFin]

end ClassicalRegister

namespace Resource.BitOpcode

/-- Operand shape fixed by one closed bit opcode. -/
@[expose, implicit_reducible]
public def inputShape : BitOpcode → CShape
  | .copy | .not => .bit
  | .and | .or | .xor => .product .bit .bit
  | .select => .product .bit (.product .bit .bit)

/-- Every closed bit opcode returns one bit. -/
@[expose, implicit_reducible]
public def outputShape : BitOpcode → CShape
  | .copy | .not | .and | .or | .xor | .select => .bit

/-- Executable semantics of one closed bit opcode. -/
@[implicit_reducible]
public def eval : (opcode : BitOpcode) → opcode.inputShape.Value → opcode.outputShape.Value
  | .copy, input => input
  | .not, .bit input => .bit (!input)
  | .and, .product (.bit left) (.bit right) => .bit (left && right)
  | .or, .product (.bit left) (.bit right) => .bit (left || right)
  | .xor, .product (.bit left) (.bit right) => .bit (Bool.xor left right)
  | .select, .product (.bit condition) (.product whenTrue whenFalse) =>
      if condition = true then whenTrue else whenFalse

@[simp] lemma inputShape_copy : inputShape .copy = .bit := rfl
@[simp] lemma inputShape_not : inputShape .not = .bit := rfl
@[simp] lemma inputShape_and : inputShape .and = .product .bit .bit := rfl
@[simp] lemma inputShape_or : inputShape .or = .product .bit .bit := rfl
@[simp] lemma inputShape_xor : inputShape .xor = .product .bit .bit := rfl
@[simp] lemma inputShape_select :
    inputShape .select = .product .bit (.product .bit .bit) := rfl
@[simp] lemma outputShape_eq (opcode : BitOpcode) : outputShape opcode = .bit := by
  cases opcode <;> rfl

end Resource.BitOpcode

namespace Resource.WordUnaryOpcode

/-- Executable fixed-width semantics of one closed unary word opcode. -/
@[implicit_reducible]
public def eval (opcode : WordUnaryOpcode) (width : Nat)
    (input : CShape.Word width) : CShape.Word width :=
  match opcode with
  | .copy => input
  | .complement => CShape.wordComplement width input
  | .increment => CShape.wordOfNat width (input.toNat + 1)
  | .decrement => CShape.wordSub width input (CShape.wordOfNat width 1)
  | .shiftLeft => CShape.wordShiftLeft width input
  | .shiftRight => CShape.wordShiftRight width input

end Resource.WordUnaryOpcode

namespace Resource.WordBinaryOpcode

/-- Result shape fixed by one closed binary word opcode. -/
@[implicit_reducible]
public def outputShape : WordBinaryOpcode → Nat → CShape
  | .equal, _ | .lessThan, _ => .bit
  | _, width => .unsignedWord width

/-- Executable fixed-width semantics of one closed binary word opcode. -/
@[implicit_reducible]
public def eval : (opcode : WordBinaryOpcode) → (width : Nat) →
    CShape.Value (.product (.unsignedWord width) (.unsignedWord width)) →
      CShape.Value (opcode.outputShape width)
  | .add, width, .product left right =>
      CShape.wordOfNat width (left.toNat + right.toNat)
  | .sub, width, .product left right => CShape.wordSub width left right
  | .mulLow, width, .product left right =>
      CShape.wordOfNat width (left.toNat * right.toNat)
  | .quotient, width, .product left right =>
      CShape.wordOfNat width (left.toNat / right.toNat)
  | .remainder, width, .product left right =>
      CShape.wordOfNat width (left.toNat % right.toNat)
  | .bitAnd, width, .product left right => CShape.wordBitAnd width left right
  | .bitOr, width, .product left right => CShape.wordBitOr width left right
  | .bitXor, width, .product left right => CShape.wordBitXor width left right
  | .equal, _width, .product left right => .bit (decide (left.toNat = right.toNat))
  | .lessThan, _width, .product left right =>
      .bit (decide (left.toNat < right.toNat))

@[simp] lemma outputShape_equal (width : Nat) : outputShape .equal width = .bit := rfl
@[simp] lemma outputShape_lessThan (width : Nat) :
    outputShape .lessThan width = .bit := rfl

end Resource.WordBinaryOpcode

/-- A computational position of one exact runtime entry in a context entry list.

Unlike proposition-valued list membership, this type-valued witness can be
eliminated by the later classical store interpreter to read and update the
corresponding heterogeneous cell. -/
public inductive RuntimeEntrySlot {kind : ProblemKind}
    (target : RuntimeEntry kind) : List (RuntimeEntry kind) → Type where
  | here {tail : List (RuntimeEntry kind)} :
      RuntimeEntrySlot target (target :: tail)
  | there {head : RuntimeEntry kind} {tail : List (RuntimeEntry kind)} :
      RuntimeEntrySlot target tail → RuntimeEntrySlot target (head :: tail)

namespace RuntimeEntrySlot

/-- Erase a computational entry position to ordinary list membership. -/
public lemma toMem {kind : ProblemKind} {target : RuntimeEntry kind}
    {entries : List (RuntimeEntry kind)} :
    RuntimeEntrySlot target entries → target ∈ entries
  | .here => .head _
  | .there slot => .tail _ slot.toMem

end RuntimeEntrySlot

/-- A computational reference to one exact closed-shape value live in a
runtime context. -/
public structure CStorageRef {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shape : CShape) where
  /-- Stable identity of the referenced live storage. -/
  key : StorageKey
  /-- The role already recorded for this storage in the context. -/
  role : StorageRole
  /-- The computational position of the exact key, role, and shape. -/
  slot : RuntimeEntrySlot (.storage key role shape) ctx.entries

namespace CStorageRef

/-- The exact referenced entry occurs in the sealed runtime context. -/
public lemma present {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (ref : CStorageRef ctx shape) :
    RuntimeEntry.storage ref.key ref.role shape ∈ ctx.entries :=
  ref.slot.toMem

/-- Reference the newly added borrowed-input entry at the head of a context. -/
public def borrowedInputHead {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    CStorageRef (ctx.addBorrowedInput key shape fresh) shape where
  key := key
  role := .borrowedInput
  slot := .here

/-- Reference the newly added workspace entry at the head of a context. -/
@[implicit_reducible]
public def workspaceHead {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    CStorageRef (ctx.addWorkspace key shape fresh) shape where
  key := key
  role := .workspace
  slot := .here

/-- Reference the newly added retained entry at the head of a context. -/
@[implicit_reducible]
public def retainedHead {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    CStorageRef (ctx.addRetained key shape fresh) shape where
  key := key
  role := .retained
  slot := .here

/-- Lift a live reference beneath one newly added borrowed input. -/
public def underBorrowedInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (ref : CStorageRef ctx shape)
    (key : StorageKey) (inputShape : CShape) (fresh : key ∉ ctx.keys) :
    CStorageRef (ctx.addBorrowedInput key inputShape fresh) shape where
  key := ref.key
  role := ref.role
  slot := .there ref.slot

/-- Lift a live reference beneath one newly added workspace entry. -/
@[implicit_reducible]
public def underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (ref : CStorageRef ctx shape)
    (key : StorageKey) (workspaceShape : CShape) (fresh : key ∉ ctx.keys) :
    CStorageRef (ctx.addWorkspace key workspaceShape fresh) shape where
  key := ref.key
  role := ref.role
  slot := .there ref.slot

/-- Lift a live reference beneath one newly added retained entry. -/
public def underRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (ref : CStorageRef ctx shape)
    (key : StorageKey) (retainedShape : CShape) (fresh : key ∉ ctx.keys) :
    CStorageRef (ctx.addRetained key retainedShape fresh) shape where
  key := ref.key
  role := ref.role
  slot := .there ref.slot

end CStorageRef

/-- A live closed-shape reference whose role permits writing a result. -/
public structure CWriteRef {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shape : CShape) extends CStorageRef ctx shape where
  /-- Borrowed inputs are read-only at this instruction boundary. -/
  writable : toCStorageRef.role ≠ .borrowedInput

namespace CWriteRef

/-- Writable reference to newly added workspace at the head of a context. -/
@[implicit_reducible]
public def workspaceHead {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    CWriteRef (ctx.addWorkspace key shape fresh) shape where
  toCStorageRef := CStorageRef.workspaceHead ctx key shape fresh
  writable := by
    change StorageRole.workspace ≠ StorageRole.borrowedInput
    decide

/-- Writable reference to a newly added retained entry at the head of a context. -/
@[implicit_reducible]
public def retainedHead {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    CWriteRef (ctx.addRetained key shape fresh) shape where
  toCStorageRef := CStorageRef.retainedHead ctx key shape fresh
  writable := by
    change StorageRole.retained ≠ StorageRole.borrowedInput
    decide

/-- Lift a writable reference beneath one newly added borrowed input. -/
public def underBorrowedInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (ref : CWriteRef ctx shape)
    (key : StorageKey) (inputShape : CShape) (fresh : key ∉ ctx.keys) :
    CWriteRef (ctx.addBorrowedInput key inputShape fresh) shape where
  toCStorageRef := ref.toCStorageRef.underBorrowedInput key inputShape fresh
  writable := ref.writable

/-- Lift a writable reference beneath one newly added workspace entry. -/
@[implicit_reducible]
public def underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (ref : CWriteRef ctx shape)
    (key : StorageKey) (workspaceShape : CShape) (fresh : key ∉ ctx.keys) :
    CWriteRef (ctx.addWorkspace key workspaceShape fresh) shape where
  toCStorageRef := ref.toCStorageRef.underWorkspace key workspaceShape fresh
  writable := ref.writable

/-- Lift a writable reference beneath one newly added retained entry. -/
public def underRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (ref : CWriteRef ctx shape)
    (key : StorageKey) (retainedShape : CShape) (fresh : key ∉ ctx.keys) :
    CWriteRef (ctx.addRetained key retainedShape fresh) shape where
  toCStorageRef := ref.toCStorageRef.underRetained key retainedShape fresh
  writable := ref.writable

end CWriteRef

/-- Closed structural operand references for classical instructions.

The constructors can only read existing storage, assemble nominal products and
fixed vectors, project nominal products, or select one statically valid
fixed-vector, bit-vector, or most-significant-bit-first word position.  They
contain no runtime callback, literal payload, or caller-defined lens. -/
public inductive CInputRef {kind : ProblemKind} (ctx : RuntimeCtx kind) : CShape → Type where
  | storage {shape : CShape} (ref : CStorageRef ctx shape) : CInputRef ctx shape
  | product {left right : CShape}
      (first : CInputRef ctx left) (second : CInputRef ctx right) :
      CInputRef ctx (.product left right)
  /-- Assemble a fixed vector from statically indexed structural operands. -/
  | fixedVector {length : Nat} {element : CShape}
      (entries : Fin length → CInputRef ctx element) :
      CInputRef ctx (.fixedVector length element)
  | first {left right : CShape}
      (input : CInputRef ctx (.product left right)) : CInputRef ctx left
  | second {left right : CShape}
      (input : CInputRef ctx (.product left right)) : CInputRef ctx right
  | vectorGet {length : Nat} {element : CShape}
      (input : CInputRef ctx (.fixedVector length element)) (index : Fin length) :
      CInputRef ctx element
  | bitsGet {width : Nat}
      (input : CInputRef ctx (.bits width)) (index : Fin width) :
      CInputRef ctx .bit
  | wordBitGet {width : Nat}
      (input : CInputRef ctx (.unsignedWord width)) (index : Fin width) :
      CInputRef ctx .bit

namespace CInputRef

/-- Lift a structural operand beneath one newly added borrowed input. -/
public def underBorrowedInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (inputShape : CShape) (fresh : key ∉ ctx.keys) :
    CInputRef (ctx.addBorrowedInput key inputShape fresh) shape :=
  match input with
  | .storage ref => .storage (ref.underBorrowedInput key inputShape fresh)
  | .product leftInput rightInput =>
      .product
        (leftInput.underBorrowedInput key inputShape fresh)
        (rightInput.underBorrowedInput key inputShape fresh)
  | .fixedVector entries =>
      .fixedVector fun index =>
        (entries index).underBorrowedInput key inputShape fresh
  | .first source => .first (source.underBorrowedInput key inputShape fresh)
  | .second source => .second (source.underBorrowedInput key inputShape fresh)
  | .vectorGet source index =>
      .vectorGet (source.underBorrowedInput key inputShape fresh) index
  | .bitsGet source index =>
      .bitsGet (source.underBorrowedInput key inputShape fresh) index
  | .wordBitGet source index =>
      .wordBitGet (source.underBorrowedInput key inputShape fresh) index

/-- Lift a structural operand beneath one newly added workspace entry. -/
@[implicit_reducible]
public def underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (workspaceShape : CShape) (fresh : key ∉ ctx.keys) :
    CInputRef (ctx.addWorkspace key workspaceShape fresh) shape :=
  match input with
  | .storage ref => .storage (ref.underWorkspace key workspaceShape fresh)
  | .product leftInput rightInput =>
      .product
        (leftInput.underWorkspace key workspaceShape fresh)
        (rightInput.underWorkspace key workspaceShape fresh)
  | .fixedVector entries =>
      .fixedVector fun index =>
        (entries index).underWorkspace key workspaceShape fresh
  | .first source => .first (source.underWorkspace key workspaceShape fresh)
  | .second source => .second (source.underWorkspace key workspaceShape fresh)
  | .vectorGet source index =>
      .vectorGet (source.underWorkspace key workspaceShape fresh) index
  | .bitsGet source index =>
      .bitsGet (source.underWorkspace key workspaceShape fresh) index
  | .wordBitGet source index =>
      .wordBitGet (source.underWorkspace key workspaceShape fresh) index

/-- Lift a structural operand beneath one newly added retained entry. -/
public def underRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (retainedShape : CShape) (fresh : key ∉ ctx.keys) :
    CInputRef (ctx.addRetained key retainedShape fresh) shape :=
  match input with
  | .storage ref => .storage (ref.underRetained key retainedShape fresh)
  | .product leftInput rightInput =>
      .product
        (leftInput.underRetained key retainedShape fresh)
        (rightInput.underRetained key retainedShape fresh)
  | .fixedVector entries =>
      .fixedVector fun index =>
        (entries index).underRetained key retainedShape fresh
  | .first source => .first (source.underRetained key retainedShape fresh)
  | .second source => .second (source.underRetained key retainedShape fresh)
  | .vectorGet source index =>
      .vectorGet (source.underRetained key retainedShape fresh) index
  | .bitsGet source index =>
      .bitsGet (source.underRetained key retainedShape fresh) index
  | .wordBitGet source index =>
      .wordBitGet (source.underRetained key retainedShape fresh) index

/-- Every storage leaf of a structural input has retained ownership.  This
permits a component to consume an assembled input without weakening the
retained-source boundary to an arbitrary caller store read. -/
def AllRetained {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape} :
    CInputRef ctx shape → Prop
  | .storage ref => ref.role = .retained
  | .product leftInput rightInput =>
      AllRetained leftInput ∧ AllRetained rightInput
  | .fixedVector entries => ∀ index, AllRetained (entries index)
  | .first input => AllRetained input
  | .second input => AllRetained input
  | .vectorGet input _index => AllRetained input
  | .bitsGet input _index => AllRetained input
  | .wordBitGet input _index => AllRetained input

/-- Lifting beneath a borrowed input preserves retained ownership of every
leaf in the structural input. -/
lemma allRetained_underBorrowedInput {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (inputShape : CShape) (fresh : key ∉ ctx.keys)
    (retained : input.AllRetained) :
    (input.underBorrowedInput key inputShape fresh).AllRetained := by
  induction input with
  | storage ref => exact retained
  | product first second firstIH secondIH =>
      exact ⟨firstIH retained.1, secondIH retained.2⟩
  | fixedVector entries entriesIH =>
      exact fun index => entriesIH index (retained index)
  | first input inputIH => exact inputIH retained
  | second input inputIH => exact inputIH retained
  | vectorGet input index inputIH => exact inputIH retained
  | bitsGet input index inputIH => exact inputIH retained
  | wordBitGet input index inputIH => exact inputIH retained

/-- Lifting beneath a workspace preserves retained ownership of every leaf in
the structural input. -/
lemma allRetained_underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (workspaceShape : CShape) (fresh : key ∉ ctx.keys)
    (retained : input.AllRetained) :
    (input.underWorkspace key workspaceShape fresh).AllRetained := by
  induction input with
  | storage ref => exact retained
  | product first second firstIH secondIH =>
      exact ⟨firstIH retained.1, secondIH retained.2⟩
  | fixedVector entries entriesIH =>
      exact fun index => entriesIH index (retained index)
  | first input inputIH => exact inputIH retained
  | second input inputIH => exact inputIH retained
  | vectorGet input index inputIH => exact inputIH retained
  | bitsGet input index inputIH => exact inputIH retained
  | wordBitGet input index inputIH => exact inputIH retained

/-- Lifting beneath another retained cell preserves retained ownership of every
leaf in the structural input. -/
lemma allRetained_underRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (retainedShape : CShape) (fresh : key ∉ ctx.keys)
    (retained : input.AllRetained) :
    (input.underRetained key retainedShape fresh).AllRetained := by
  induction input with
  | storage ref => exact retained
  | product first second firstIH secondIH =>
      exact ⟨firstIH retained.1, secondIH retained.2⟩
  | fixedVector entries entriesIH =>
      exact fun index => entriesIH index (retained index)
  | first input inputIH => exact inputIH retained
  | second input inputIH => exact inputIH retained
  | vectorGet input index inputIH => exact inputIH retained
  | bitsGet input index inputIH => exact inputIH retained
  | wordBitGet input index inputIH => exact inputIH retained

end CInputRef

/-- Closed, shape- and context-indexed classical machine instructions.

All atomic instructions preserve their exact runtime context. Allocation,
retention, and lexical workspace are explicit circuit operations; the complete
Output names every value and physical system that remains live. -/
public inductive ClassicalOp {kind : ProblemKind} :
    CShape → CShape → RuntimeCtx kind → RuntimeCtx kind → Type where
  | bit (opcode : Resource.BitOpcode) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx opcode.inputShape)
      (output : CWriteRef ctx opcode.outputShape) :
      ClassicalOp opcode.inputShape opcode.outputShape ctx ctx
  | wordUnary (opcode : Resource.WordUnaryOpcode) (width : Nat)
      (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.unsignedWord width))
      (output : CWriteRef ctx (.unsignedWord width)) :
      ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx
  | wordBinary (opcode : Resource.WordBinaryOpcode) (width : Nat)
      (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.product (.unsignedWord width) (.unsignedWord width)))
      (output : CWriteRef ctx (opcode.outputShape width)) :
      ClassicalOp
        (.product (.unsignedWord width) (.unsignedWord width))
        (opcode.outputShape width) ctx ctx
  | wordResize (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.unsignedWord sourceWidth))
      (output : CWriteRef ctx (.unsignedWord targetWidth)) :
      ClassicalOp (.unsignedWord sourceWidth) (.unsignedWord targetWidth) ctx ctx
  | addCarry (width : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.product (.unsignedWord width) (.unsignedWord width)))
      (output : CWriteRef ctx (.product (.unsignedWord width) .bit)) :
      ClassicalOp
        (.product (.unsignedWord width) (.unsignedWord width))
        (.product (.unsignedWord width) .bit) ctx ctx
  | subBorrow (width : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.product (.unsignedWord width) (.unsignedWord width)))
      (output : CWriteRef ctx (.product (.unsignedWord width) .bit)) :
      ClassicalOp
        (.product (.unsignedWord width) (.unsignedWord width))
        (.product (.unsignedWord width) .bit) ctx ctx
  | mulFull (leftWidth rightWidth : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth)))
      (output : CWriteRef ctx (.unsignedWord (leftWidth + rightWidth))) :
      ClassicalOp
        (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth))
        (.unsignedWord (leftWidth + rightWidth)) ctx ctx
  | divRem (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
      (output : CWriteRef ctx
        (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))) :
      ClassicalOp
        (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))
        (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)) ctx ctx
  /-- Copy actual binary finite-register readings into an ordered bit string. -/
  | packFiniteBits (count : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.fixedVector count (.finite 2)))
      (output : CWriteRef ctx (.bits count)) :
      ClassicalOp (.fixedVector count (.finite 2)) (.bits count) ctx ctx
  /-- Materialize a possibly virtual structural product in one writable slot. -/
  | packProduct {left right : CShape} (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.product left right))
      (output : CWriteRef ctx (.product left right)) :
      ClassicalOp (.product left right) (.product left right) ctx ctx
  /-- Preserve a raw word while changing only its nominal signed shape. -/
  | packBoundedSignedWord (width : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.unsignedWord width))
      (output : CWriteRef ctx (.boundedSignedWord width)) :
      ClassicalOp (.unsignedWord width) (.boundedSignedWord width) ctx ctx
  /-- Materialize a Boolean tag and payload as an optional encoding. -/
  | packOption {payload : CShape} (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.product .bit payload))
      (output : CWriteRef ctx (.option payload)) :
      ClassicalOp (.product .bit payload) (.option payload) ctx ctx
  /-- Expose an optional tag and payload in one writable product encoding. -/
  | unpackOption {payload : CShape} (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.option payload))
      (output : CWriteRef ctx (.product .bit payload)) :
      ClassicalOp (.option payload) (.product .bit payload) ctx ctx
  /-- Erase only the nominal unit-residue wrapper around a raw word. -/
  | unpackUnitResidue (width : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.unitResidue width))
      (output : CWriteRef ctx (.unsignedWord width)) :
      ClassicalOp (.unitResidue width) (.unsignedWord width) ctx ctx
  | unpackCanonicalResidue (width : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.canonicalResidue width))
      (output : CWriteRef ctx (.unsignedWord width)) :
      ClassicalOp (.canonicalResidue width) (.unsignedWord width) ctx ctx
  | packCanonicalResidue (width : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.unsignedWord width))
      (output : CWriteRef ctx (.canonicalResidue width)) :
      ClassicalOp (.unsignedWord width) (.canonicalResidue width) ctx ctx
  /-- Expose raw point storage without semantic decoding or validation. -/
  | unpackEllipticCurvePoint (width : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx (.ellipticCurvePoint width))
      (output : CWriteRef ctx
        (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))) :
      ClassicalOp
        (.ellipticCurvePoint width)
        (.product .bit (.product (.unsignedWord width) (.unsignedWord width))) ctx ctx
  /-- Materialize raw point storage without semantic decoding or validation. -/
  | packEllipticCurvePoint (width : Nat) (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
      (output : CWriteRef ctx (.ellipticCurvePoint width)) :
      ClassicalOp
        (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))
        (.ellipticCurvePoint width) ctx ctx
  | vectorRead (length elementWidth : Nat) (index : Fin length)
      (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.fixedVector length (.unsignedWord elementWidth)))
      (output : CWriteRef ctx (.unsignedWord elementWidth)) :
      ClassicalOp
        (.fixedVector length (.unsignedWord elementWidth))
        (.unsignedWord elementWidth) ctx ctx
  | vectorWrite (length elementWidth : Nat) (index : Fin length)
      (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.product (.fixedVector length (.unsignedWord elementWidth))
          (.unsignedWord elementWidth)))
      (output : CWriteRef ctx
        (.fixedVector length (.unsignedWord elementWidth))) :
      ClassicalOp
        (.product (.fixedVector length (.unsignedWord elementWidth))
          (.unsignedWord elementWidth))
        (.fixedVector length (.unsignedWord elementWidth)) ctx ctx
  | vectorSwap (length elementWidth : Nat) (left right : Fin length)
      (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.fixedVector length (.unsignedWord elementWidth)))
      (output : CWriteRef ctx
        (.fixedVector length (.unsignedWord elementWidth))) :
      ClassicalOp
        (.fixedVector length (.unsignedWord elementWidth))
        (.fixedVector length (.unsignedWord elementWidth)) ctx ctx
  | vectorRowXor (length elementWidth : Nat) (source destination : Fin length)
      (ctx : RuntimeCtx kind)
      (input : CInputRef ctx
        (.fixedVector length (.unsignedWord elementWidth)))
      (output : CWriteRef ctx
        (.fixedVector length (.unsignedWord elementWidth))) :
      ClassicalOp
        (.fixedVector length (.unsignedWord elementWidth))
        (.fixedVector length (.unsignedWord elementWidth)) ctx ctx

namespace ClassicalOp

/-- Structural operand reference carried by an instruction constructor. -/
@[implicit_reducible]
public def inputRef {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind} :
    ClassicalOp input output pre post → CInputRef pre input
  | .bit _opcode _ctx input _output => input
  | .wordUnary _opcode _width _ctx input _output => input
  | .wordBinary _opcode _width _ctx input _output => input
  | .wordResize _sourceWidth _targetWidth _ctx input _output => input
  | .addCarry _width _ctx input _output => input
  | .subBorrow _width _ctx input _output => input
  | .mulFull _leftWidth _rightWidth _ctx input _output => input
  | .divRem _numeratorWidth _divisorWidth _ctx input _output => input
  | .packProduct _ctx input _output => input
  | .packFiniteBits _count _ctx input _output => input
  | .packBoundedSignedWord _width _ctx input _output => input
  | .packOption _ctx input _output => input
  | .unpackOption _ctx input _output => input
  | .unpackUnitResidue _width _ctx input _output => input
  | .unpackCanonicalResidue _width _ctx input _output => input
  | .packCanonicalResidue _width _ctx input _output => input
  | .unpackEllipticCurvePoint _width _ctx input _output => input
  | .packEllipticCurvePoint _width _ctx input _output => input
  | .vectorRead _length _elementWidth _index _ctx input _output => input
  | .vectorWrite _length _elementWidth _index _ctx input _output => input
  | .vectorSwap _length _elementWidth _left _right _ctx input _output => input
  | .vectorRowXor _length _elementWidth _source _destination _ctx input _output =>
      input

/-- Writable result reference carried by an instruction constructor. -/
@[implicit_reducible]
public def outputRef {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind} :
    ClassicalOp input output pre post → CWriteRef post output
  | .bit _opcode _ctx _input output => output
  | .wordUnary _opcode _width _ctx _input output => output
  | .wordBinary _opcode _width _ctx _input output => output
  | .wordResize _sourceWidth _targetWidth _ctx _input output => output
  | .addCarry _width _ctx _input output => output
  | .subBorrow _width _ctx _input output => output
  | .mulFull _leftWidth _rightWidth _ctx _input output => output
  | .divRem _numeratorWidth _divisorWidth _ctx _input output => output
  | .packProduct _ctx _input output => output
  | .packFiniteBits _count _ctx _input output => output
  | .packBoundedSignedWord _width _ctx _input output => output
  | .packOption _ctx _input output => output
  | .unpackOption _ctx _input output => output
  | .unpackUnitResidue _width _ctx _input output => output
  | .unpackCanonicalResidue _width _ctx _input output => output
  | .packCanonicalResidue _width _ctx _input output => output
  | .unpackEllipticCurvePoint _width _ctx _input output => output
  | .packEllipticCurvePoint _width _ctx _input output => output
  | .vectorRead _length _elementWidth _index _ctx _input output => output
  | .vectorWrite _length _elementWidth _index _ctx _input output => output
  | .vectorSwap _length _elementWidth _left _right _ctx _input output => output
  | .vectorRowXor _length _elementWidth _source _destination _ctx _input output =>
      output

@[simp] lemma inputRef_wordResize {kind : ProblemKind}
    (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord targetWidth)) :
    (ClassicalOp.wordResize sourceWidth targetWidth ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_wordResize {kind : ProblemKind}
    (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord targetWidth)) :
    (ClassicalOp.wordResize sourceWidth targetWidth ctx input output).outputRef = output :=
  rfl

@[simp] lemma inputRef_packProduct {kind : ProblemKind}
    {left right : CShape} (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.product left right))
    (output : CWriteRef ctx (.product left right)) :
    (ClassicalOp.packProduct ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_packProduct {kind : ProblemKind}
    {left right : CShape} (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.product left right))
    (output : CWriteRef ctx (.product left right)) :
    (ClassicalOp.packProduct ctx input output).outputRef = output :=
  rfl

@[simp] lemma inputRef_packBoundedSignedWord {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.boundedSignedWord width)) :
    (ClassicalOp.packBoundedSignedWord width ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_packBoundedSignedWord {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.boundedSignedWord width)) :
    (ClassicalOp.packBoundedSignedWord width ctx input output).outputRef = output :=
  rfl

@[simp] lemma inputRef_packOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.product .bit payload))
    (output : CWriteRef ctx (.option payload)) :
    (ClassicalOp.packOption ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_packOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.product .bit payload))
    (output : CWriteRef ctx (.option payload)) :
    (ClassicalOp.packOption ctx input output).outputRef = output :=
  rfl

@[simp] lemma inputRef_unpackOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.option payload))
    (output : CWriteRef ctx (.product .bit payload)) :
    (ClassicalOp.unpackOption ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_unpackOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.option payload))
    (output : CWriteRef ctx (.product .bit payload)) :
    (ClassicalOp.unpackOption ctx input output).outputRef = output :=
  rfl

@[simp] lemma inputRef_unpackUnitResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.unitResidue width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackUnitResidue width ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_unpackUnitResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.unitResidue width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackUnitResidue width ctx input output).outputRef = output :=
  rfl

@[simp] lemma inputRef_unpackCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.canonicalResidue width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackCanonicalResidue width ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_unpackCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.canonicalResidue width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackCanonicalResidue width ctx input output).outputRef = output :=
  rfl

@[simp] lemma inputRef_packCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.canonicalResidue width)) :
    (ClassicalOp.packCanonicalResidue width ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_packCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.canonicalResidue width)) :
    (ClassicalOp.packCanonicalResidue width ctx input output).outputRef = output :=
  rfl

@[simp] lemma inputRef_unpackEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.ellipticCurvePoint width))
    (output : CWriteRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))) :
    (ClassicalOp.unpackEllipticCurvePoint width ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_unpackEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx (.ellipticCurvePoint width))
    (output : CWriteRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))) :
    (ClassicalOp.unpackEllipticCurvePoint width ctx input output).outputRef = output :=
  rfl

@[simp] lemma inputRef_packEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (output : CWriteRef ctx (.ellipticCurvePoint width)) :
    (ClassicalOp.packEllipticCurvePoint width ctx input output).inputRef = input :=
  rfl

@[simp] lemma outputRef_packEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (input : CInputRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (output : CWriteRef ctx (.ellipticCurvePoint width)) :
    (ClassicalOp.packEllipticCurvePoint width ctx input output).outputRef = output :=
  rfl

/-- A routine instruction may write only lexical workspace or a retained
result. Final-output designation belongs to the later typed-run boundary. -/
@[implicit_reducible]
def RoutineWritable {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind} (op : ClassicalOp input output pre post) : Prop :=
  op.outputRef.toCStorageRef.role = .workspace ∨
    op.outputRef.toCStorageRef.role = .retained

/-- Execute the semantics fixed by an instruction constructor. -/
@[implicit_reducible]
public def eval {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind} :
    ClassicalOp input output pre post → input.Value → output.Value
  | .bit opcode _ctx _input _output, value => opcode.eval value
  | .wordUnary opcode width _ctx _input _output, value => opcode.eval width value
  | .wordBinary opcode width _ctx _input _output, value => opcode.eval width value
  | .wordResize _sourceWidth targetWidth _ctx _input _output, value =>
      CShape.wordResize targetWidth value
  | .addCarry width _ctx _input _output, value => CShape.addCarry width value
  | .subBorrow width _ctx _input _output, value => CShape.subBorrow width value
  | .mulFull leftWidth rightWidth _ctx _input _output, value =>
      CShape.mulFull leftWidth rightWidth value
  | .divRem numeratorWidth divisorWidth _ctx _input _output, value =>
      CShape.divRem numeratorWidth divisorWidth value
  | .packProduct _ctx _input _output, value => CShape.packProduct value
  | .packFiniteBits count _ctx _input _output, value => CShape.packFiniteBits count value
  | .packBoundedSignedWord width _ctx _input _output, value =>
      CShape.packBoundedSignedWord width value
  | .packOption _ctx _input _output, value => CShape.packOption value
  | .unpackOption _ctx _input _output, value => CShape.unpackOption value
  | .unpackUnitResidue width _ctx _input _output, value =>
      CShape.unpackUnitResidue width value
  | .unpackCanonicalResidue width _ctx _input _output, value =>
      CShape.unpackCanonicalResidue width value
  | .packCanonicalResidue width _ctx _input _output, value =>
      CShape.packCanonicalResidue width value
  | .unpackEllipticCurvePoint width _ctx _input _output, value =>
      CShape.unpackEllipticCurvePoint width value
  | .packEllipticCurvePoint width _ctx _input _output, value =>
      CShape.packEllipticCurvePoint width value
  | .vectorRead _length _elementWidth index _ctx _input _output, value =>
      value.get index
  | .vectorWrite _length _elementWidth index _ctx _input _output,
      .product vector newValue =>
      CShape.vectorWrite vector index newValue
  | .vectorSwap _length _elementWidth left right _ctx _input _output, value =>
      CShape.vectorSwap value left right
  | .vectorRowXor _length _elementWidth source destination _ctx _input _output, value =>
      CShape.vectorRowXor value source destination

/-- The closed accounting label selected by an instruction constructor. -/
public def label {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind} :
    ClassicalOp input output pre post → Resource.ClassicalOpLabel
  | .bit opcode _ctx _input _output => .bit opcode
  | .wordUnary opcode width _ctx _input _output => .wordUnary opcode width
  | .wordBinary opcode width _ctx _input _output => .wordBinary opcode width
  | .wordResize sourceWidth targetWidth _ctx _input _output =>
      .wordResize sourceWidth targetWidth
  | .addCarry width _ctx _input _output => .addCarry width
  | .subBorrow width _ctx _input _output => .subBorrow width
  | .mulFull leftWidth rightWidth _ctx _input _output => .mulFull leftWidth rightWidth
  | .divRem numeratorWidth divisorWidth _ctx _input _output =>
      .divRem numeratorWidth divisorWidth
  | .packProduct (left := left) (right := right) _ctx _input _output =>
      .nominalEncoding (.packProduct left.bitWidth right.bitWidth)
  | .packFiniteBits count _ctx _input _output => .nominalEncoding (.packFiniteBits count)
  | .packBoundedSignedWord width _ctx _input _output =>
      .nominalEncoding (.packBoundedSignedWord width)
  | .packOption (payload := payload) _ctx _input _output =>
      .nominalEncoding (.packOption payload.bitWidth)
  | .unpackOption (payload := payload) _ctx _input _output =>
      .nominalEncoding (.unpackOption payload.bitWidth)
  | .unpackUnitResidue width _ctx _input _output =>
      .nominalEncoding (.unpackUnitResidue width)
  | .unpackCanonicalResidue width _ctx _input _output =>
      .residueEncoding .unpack width
  | .packCanonicalResidue width _ctx _input _output =>
      .residueEncoding .pack width
  | .unpackEllipticCurvePoint width _ctx _input _output =>
      .nominalEncoding (.unpackEllipticCurvePoint width)
  | .packEllipticCurvePoint width _ctx _input _output =>
      .nominalEncoding (.packEllipticCurvePoint width)
  | .vectorRead length elementWidth _index _ctx _input _output =>
      .vector .read length elementWidth
  | .vectorWrite length elementWidth _index _ctx _input _output =>
      .vector .write length elementWidth
  | .vectorSwap length elementWidth _left _right _ctx _input _output =>
      .vector .swap length elementWidth
  | .vectorRowXor length elementWidth _source _destination _ctx _input _output =>
      .vector .rowXor length elementWidth

/-- The local liveness flow fixed by the same instruction constructor. -/
def flow {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind} :
    (op : ClassicalOp input output pre post) → SpaceFlow pre post
  | .bit _opcode ctx _input _output => SpaceFlow.stay ctx
  | .wordUnary _opcode _width ctx _input _output => SpaceFlow.stay ctx
  | .wordBinary _opcode _width ctx _input _output => SpaceFlow.stay ctx
  | .wordResize _sourceWidth _targetWidth ctx _input _output => SpaceFlow.stay ctx
  | .addCarry _width ctx _input _output => SpaceFlow.stay ctx
  | .subBorrow _width ctx _input _output => SpaceFlow.stay ctx
  | .mulFull _leftWidth _rightWidth ctx _input _output => SpaceFlow.stay ctx
  | .divRem _numeratorWidth _divisorWidth ctx _input _output => SpaceFlow.stay ctx
  | .packProduct ctx _input _output => SpaceFlow.stay ctx
  | .packFiniteBits _count ctx _input _output => SpaceFlow.stay ctx
  | .packBoundedSignedWord _width ctx _input _output => SpaceFlow.stay ctx
  | .packOption ctx _input _output => SpaceFlow.stay ctx
  | .unpackOption ctx _input _output => SpaceFlow.stay ctx
  | .unpackUnitResidue _width ctx _input _output => SpaceFlow.stay ctx
  | .unpackCanonicalResidue _width ctx _input _output => SpaceFlow.stay ctx
  | .packCanonicalResidue _width ctx _input _output => SpaceFlow.stay ctx
  | .unpackEllipticCurvePoint _width ctx _input _output => SpaceFlow.stay ctx
  | .packEllipticCurvePoint _width ctx _input _output => SpaceFlow.stay ctx
  | .vectorRead _length _elementWidth _index ctx _input _output => SpaceFlow.stay ctx
  | .vectorWrite _length _elementWidth _index ctx _input _output => SpaceFlow.stay ctx
  | .vectorSwap _length _elementWidth _left _right ctx _input _output =>
      SpaceFlow.stay ctx
  | .vectorRowXor _length _elementWidth _source _destination ctx _input _output =>
      SpaceFlow.stay ctx

/-- Operand width fixed by one instruction constructor. -/
def inputBitWidth {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind} :
    ClassicalOp input output pre post → Nat
  | .bit opcode _ctx _input _output => opcode.inputShape.bitWidth
  | .wordUnary _opcode width _ctx _input _output => width
  | .wordBinary _opcode width _ctx _input _output => width + width
  | .wordResize sourceWidth _targetWidth _ctx _input _output => sourceWidth
  | .addCarry width _ctx _input _output => width + width
  | .subBorrow width _ctx _input _output => width + width
  | .mulFull leftWidth rightWidth _ctx _input _output => leftWidth + rightWidth
  | .divRem numeratorWidth divisorWidth _ctx _input _output =>
      numeratorWidth + divisorWidth
  | .packProduct (left := left) (right := right) _ctx _input _output =>
      left.bitWidth + right.bitWidth
  | .packFiniteBits count _ctx _input _output => (CShape.fixedVector count (.finite 2)).bitWidth
  | .packBoundedSignedWord width _ctx _input _output => width
  | .packOption (payload := payload) _ctx _input _output =>
      1 + payload.bitWidth
  | .unpackOption (payload := payload) _ctx _input _output =>
      1 + payload.bitWidth
  | .unpackUnitResidue width _ctx _input _output => width
  | .unpackCanonicalResidue width _ctx _input _output => width
  | .packCanonicalResidue width _ctx _input _output => width
  | .unpackEllipticCurvePoint width _ctx _input _output => 1 + 2 * width
  | .packEllipticCurvePoint width _ctx _input _output => 1 + (width + width)
  | .vectorRead length elementWidth _index _ctx _input _output =>
      length * elementWidth
  | .vectorWrite length elementWidth _index _ctx _input _output =>
      length * elementWidth + elementWidth
  | .vectorSwap length elementWidth _left _right _ctx _input _output =>
      length * elementWidth
  | .vectorRowXor length elementWidth _source _destination _ctx _input _output =>
      length * elementWidth

/-- Result width fixed by one instruction constructor. -/
def outputBitWidth {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind} :
    ClassicalOp input output pre post → Nat
  | .bit opcode _ctx _input _output => opcode.outputShape.bitWidth
  | .wordUnary _opcode width _ctx _input _output => width
  | .wordBinary opcode width _ctx _input _output =>
      (opcode.outputShape width).bitWidth
  | .wordResize _sourceWidth targetWidth _ctx _input _output => targetWidth
  | .addCarry width _ctx _input _output => width + 1
  | .subBorrow width _ctx _input _output => width + 1
  | .mulFull leftWidth rightWidth _ctx _input _output => leftWidth + rightWidth
  | .divRem numeratorWidth divisorWidth _ctx _input _output =>
      numeratorWidth + divisorWidth
  | .packProduct (left := left) (right := right) _ctx _input _output =>
      left.bitWidth + right.bitWidth
  | .packFiniteBits count _ctx _input _output => count
  | .packBoundedSignedWord width _ctx _input _output => width
  | .packOption (payload := payload) _ctx _input _output =>
      1 + payload.bitWidth
  | .unpackOption (payload := payload) _ctx _input _output =>
      1 + payload.bitWidth
  | .unpackUnitResidue width _ctx _input _output => width
  | .unpackCanonicalResidue width _ctx _input _output => width
  | .packCanonicalResidue width _ctx _input _output => width
  | .unpackEllipticCurvePoint width _ctx _input _output => 1 + (width + width)
  | .packEllipticCurvePoint width _ctx _input _output => 1 + 2 * width
  | .vectorRead _length elementWidth _index _ctx _input _output => elementWidth
  | .vectorWrite length elementWidth _index _ctx _input _output =>
      length * elementWidth
  | .vectorSwap length elementWidth _left _right _ctx _input _output =>
      length * elementWidth
  | .vectorRowXor length elementWidth _source _destination _ctx _input _output =>
      length * elementWidth

/-- Local executable specification induced by one instruction. -/
def EvaluatesTo {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind}
    (op : ClassicalOp input output pre post)
    (operand : input.Value) (result : output.Value) : Prop :=
  op.eval operand = result

/-- Evaluation satisfies the instruction's own closed local specification. -/
lemma eval_correct {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind}
    (op : ClassicalOp input output pre post) (operand : input.Value) :
    op.EvaluatesTo operand (op.eval operand) :=
  rfl

@[simp] lemma eval_bit {kind : ProblemKind}
    (opcode : Resource.BitOpcode) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx opcode.inputShape)
    (outputRef : CWriteRef ctx opcode.outputShape)
    (operand : opcode.inputShape.Value) :
    (ClassicalOp.bit opcode ctx inputRef outputRef).eval operand = opcode.eval operand :=
  rfl

@[simp] lemma eval_wordUnary {kind : ProblemKind}
    (opcode : Resource.WordUnaryOpcode) (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.unsignedWord width))
    (operand : CShape.Word width) :
    (ClassicalOp.wordUnary opcode width ctx inputRef outputRef).eval operand =
      opcode.eval width operand :=
  rfl

@[simp] lemma eval_wordBinary {kind : ProblemKind}
    (opcode : Resource.WordBinaryOpcode) (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (opcode.outputShape width))
    (operand : CShape.Value
      (.product (.unsignedWord width) (.unsignedWord width))) :
    (ClassicalOp.wordBinary opcode width ctx inputRef outputRef).eval operand =
      opcode.eval width operand :=
  rfl

@[simp] lemma eval_wordResize {kind : ProblemKind}
    (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord sourceWidth))
    (outputRef : CWriteRef ctx (.unsignedWord targetWidth))
    (operand : CShape.Word sourceWidth) :
    (ClassicalOp.wordResize sourceWidth targetWidth ctx inputRef outputRef).eval
        operand =
      CShape.wordResize targetWidth operand :=
  rfl

@[simp] lemma eval_addCarry {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit))
    (operand : CShape.Value
      (.product (.unsignedWord width) (.unsignedWord width))) :
    (ClassicalOp.addCarry width ctx inputRef outputRef).eval operand =
      CShape.addCarry width operand :=
  rfl

@[simp] lemma eval_subBorrow {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit))
    (operand : CShape.Value
      (.product (.unsignedWord width) (.unsignedWord width))) :
    (ClassicalOp.subBorrow width ctx inputRef outputRef).eval operand =
      CShape.subBorrow width operand :=
  rfl

@[simp] lemma eval_mulFull {kind : ProblemKind}
    (leftWidth rightWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth)))
    (outputRef : CWriteRef ctx (.unsignedWord (leftWidth + rightWidth)))
    (operand : CShape.Value
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth))) :
    (ClassicalOp.mulFull leftWidth rightWidth ctx inputRef outputRef).eval operand =
      CShape.mulFull leftWidth rightWidth operand :=
  rfl

@[simp] lemma eval_divRem {kind : ProblemKind}
    (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (outputRef : CWriteRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (operand : CShape.Value
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))) :
    (ClassicalOp.divRem numeratorWidth divisorWidth ctx inputRef outputRef).eval operand =
      CShape.divRem numeratorWidth divisorWidth operand :=
  rfl

@[simp] lemma eval_packProduct {kind : ProblemKind}
    {left right : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product left right))
    (outputRef : CWriteRef ctx (.product left right))
    (operand : CShape.Value (.product left right)) :
    (ClassicalOp.packProduct ctx inputRef outputRef).eval operand =
      CShape.packProduct operand :=
  rfl

@[simp] lemma eval_packBoundedSignedWord {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.boundedSignedWord width))
    (operand : CShape.Word width) :
    (ClassicalOp.packBoundedSignedWord width ctx inputRef outputRef).eval operand =
      CShape.packBoundedSignedWord width operand :=
  rfl

@[simp] lemma eval_packOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product .bit payload))
    (outputRef : CWriteRef ctx (.option payload))
    (operand : CShape.Value (.product .bit payload)) :
    (ClassicalOp.packOption ctx inputRef outputRef).eval operand =
      CShape.packOption operand :=
  rfl

@[simp] lemma eval_unpackOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.option payload))
    (outputRef : CWriteRef ctx (.product .bit payload))
    (operand : CShape.Value (.option payload)) :
    (ClassicalOp.unpackOption ctx inputRef outputRef).eval operand =
      CShape.unpackOption operand :=
  rfl

@[simp] lemma eval_unpackUnitResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unitResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width))
    (operand : CShape.Value (.unitResidue width)) :
    (ClassicalOp.unpackUnitResidue width ctx inputRef outputRef).eval operand =
      CShape.unpackUnitResidue width operand :=
  rfl

@[simp] lemma eval_unpackCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.canonicalResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width))
    (operand : CShape.Value (.canonicalResidue width)) :
    (ClassicalOp.unpackCanonicalResidue width ctx inputRef outputRef).eval operand =
      CShape.unpackCanonicalResidue width operand :=
  rfl

@[simp] lemma eval_packCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.canonicalResidue width))
    (operand : CShape.Word width) :
    (ClassicalOp.packCanonicalResidue width ctx inputRef outputRef).eval operand =
      CShape.packCanonicalResidue width operand :=
  rfl

@[simp] lemma eval_unpackEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.ellipticCurvePoint width))
    (outputRef : CWriteRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (operand : CShape.Value (.ellipticCurvePoint width)) :
    (ClassicalOp.unpackEllipticCurvePoint width ctx inputRef outputRef).eval operand =
      CShape.unpackEllipticCurvePoint width operand :=
  rfl

@[simp] lemma eval_packEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (outputRef : CWriteRef ctx (.ellipticCurvePoint width))
    (operand : CShape.Value
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))) :
    (ClassicalOp.packEllipticCurvePoint width ctx inputRef outputRef).eval operand =
      CShape.packEllipticCurvePoint width operand :=
  rfl

@[simp] lemma eval_vectorRead {kind : ProblemKind}
    (length elementWidth : Nat) (index : Fin length) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx (.unsignedWord elementWidth))
    (operand : CShape.Value
      (.fixedVector length (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorRead length elementWidth index ctx inputRef outputRef).eval
      operand = operand.get index :=
  rfl

@[simp] lemma eval_vectorWrite {kind : ProblemKind}
    (length elementWidth : Nat) (index : Fin length) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.fixedVector length (.unsignedWord elementWidth))
        (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (operand : CShape.Value
      (.product (.fixedVector length (.unsignedWord elementWidth))
        (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorWrite length elementWidth index ctx inputRef outputRef).eval
      operand = CShape.vectorWrite operand.first index operand.second :=
  by
    cases operand
    rfl

@[simp] lemma eval_vectorSwap {kind : ProblemKind}
    (length elementWidth : Nat) (left right : Fin length)
    (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (operand : CShape.Value
      (.fixedVector length (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorSwap length elementWidth left right ctx inputRef outputRef).eval
      operand =
      CShape.vectorSwap operand left right :=
  rfl

@[simp] lemma eval_vectorRowXor {kind : ProblemKind}
    (length elementWidth : Nat) (source destination : Fin length)
    (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (operand : CShape.Value
      (.fixedVector length (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorRowXor length elementWidth source destination ctx
      inputRef outputRef).eval operand =
      CShape.vectorRowXor operand source destination :=
  rfl

@[simp] lemma label_wordResize {kind : ProblemKind}
    (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord sourceWidth))
    (outputRef : CWriteRef ctx (.unsignedWord targetWidth)) :
    (ClassicalOp.wordResize sourceWidth targetWidth ctx inputRef outputRef).label =
      .wordResize sourceWidth targetWidth :=
  rfl

@[simp] lemma label_packProduct {kind : ProblemKind}
    {left right : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product left right))
    (outputRef : CWriteRef ctx (.product left right)) :
    (ClassicalOp.packProduct ctx inputRef outputRef).label =
      .nominalEncoding (.packProduct left.bitWidth right.bitWidth) :=
  rfl

@[simp] lemma label_packBoundedSignedWord {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.boundedSignedWord width)) :
    (ClassicalOp.packBoundedSignedWord width ctx inputRef outputRef).label =
      .nominalEncoding (.packBoundedSignedWord width) :=
  rfl

@[simp] lemma label_packOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product .bit payload))
    (outputRef : CWriteRef ctx (.option payload)) :
    (ClassicalOp.packOption ctx inputRef outputRef).label =
      .nominalEncoding (.packOption payload.bitWidth) :=
  rfl

@[simp] lemma label_unpackOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.option payload))
    (outputRef : CWriteRef ctx (.product .bit payload)) :
    (ClassicalOp.unpackOption ctx inputRef outputRef).label =
      .nominalEncoding (.unpackOption payload.bitWidth) :=
  rfl

@[simp] lemma label_unpackUnitResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unitResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackUnitResidue width ctx inputRef outputRef).label =
      .nominalEncoding (.unpackUnitResidue width) :=
  rfl

@[simp] lemma label_unpackCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.canonicalResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackCanonicalResidue width ctx inputRef outputRef).label =
      .residueEncoding .unpack width :=
  rfl

@[simp] lemma label_packCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.canonicalResidue width)) :
    (ClassicalOp.packCanonicalResidue width ctx inputRef outputRef).label =
      .residueEncoding .pack width :=
  rfl

@[simp] lemma label_unpackEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.ellipticCurvePoint width))
    (outputRef : CWriteRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))) :
    (ClassicalOp.unpackEllipticCurvePoint width ctx inputRef outputRef).label =
      .nominalEncoding (.unpackEllipticCurvePoint width) :=
  rfl

@[simp] lemma label_packEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (outputRef : CWriteRef ctx (.ellipticCurvePoint width)) :
    (ClassicalOp.packEllipticCurvePoint width ctx inputRef outputRef).label =
      .nominalEncoding (.packEllipticCurvePoint width) :=
  rfl

@[simp] lemma flow_wordResize {kind : ProblemKind}
    (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord sourceWidth))
    (outputRef : CWriteRef ctx (.unsignedWord targetWidth)) :
    (ClassicalOp.wordResize sourceWidth targetWidth ctx inputRef outputRef).flow =
      SpaceFlow.stay ctx :=
  rfl

@[simp] lemma flow_packProduct {kind : ProblemKind}
    {left right : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product left right))
    (outputRef : CWriteRef ctx (.product left right)) :
    (ClassicalOp.packProduct ctx inputRef outputRef).flow = SpaceFlow.stay ctx :=
  rfl

@[simp] lemma flow_packBoundedSignedWord {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.boundedSignedWord width)) :
    (ClassicalOp.packBoundedSignedWord width ctx inputRef outputRef).flow =
      SpaceFlow.stay ctx :=
  rfl

@[simp] lemma flow_packOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product .bit payload))
    (outputRef : CWriteRef ctx (.option payload)) :
    (ClassicalOp.packOption ctx inputRef outputRef).flow = SpaceFlow.stay ctx :=
  rfl

@[simp] lemma flow_unpackOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.option payload))
    (outputRef : CWriteRef ctx (.product .bit payload)) :
    (ClassicalOp.unpackOption ctx inputRef outputRef).flow = SpaceFlow.stay ctx :=
  rfl

@[simp] lemma flow_unpackUnitResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unitResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackUnitResidue width ctx inputRef outputRef).flow =
      SpaceFlow.stay ctx :=
  rfl

@[simp] lemma flow_unpackCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.canonicalResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackCanonicalResidue width ctx inputRef outputRef).flow =
      SpaceFlow.stay ctx :=
  rfl

@[simp] lemma flow_packCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.canonicalResidue width)) :
    (ClassicalOp.packCanonicalResidue width ctx inputRef outputRef).flow =
      SpaceFlow.stay ctx :=
  rfl

@[simp] lemma flow_unpackEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.ellipticCurvePoint width))
    (outputRef : CWriteRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))) :
    (ClassicalOp.unpackEllipticCurvePoint width ctx inputRef outputRef).flow =
      SpaceFlow.stay ctx :=
  rfl

@[simp] lemma flow_packEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (outputRef : CWriteRef ctx (.ellipticCurvePoint width)) :
    (ClassicalOp.packEllipticCurvePoint width ctx inputRef outputRef).flow =
      SpaceFlow.stay ctx :=
  rfl

/-- Every admitted atomic instruction preserves its exact live context. -/
lemma pre_eq_post {kind : ProblemKind} {input output : CShape}
    {pre post : RuntimeCtx kind}
    (op : ClassicalOp input output pre post) : pre = post := by
  cases op <;> rfl

@[simp] lemma peakResidentSpace_flow {kind : ProblemKind}
    {input output : CShape} {pre post : RuntimeCtx kind}
    (op : ClassicalOp input output pre post) :
    op.flow.peakResidentSpace = pre.residentSpace := by
  cases op <;> rfl

@[simp] lemma peakAuxiliarySpace_flow {kind : ProblemKind}
    {input output : CShape} {pre post : RuntimeCtx kind}
    (op : ClassicalOp input output pre post) :
    op.flow.peakAuxiliarySpace = pre.auxiliarySpace := by
  cases op <;> rfl

@[simp] lemma inputBitWidth_eq_shape {kind : ProblemKind}
    {input output : CShape} {pre post : RuntimeCtx kind}
    (op : ClassicalOp input output pre post) :
    op.inputBitWidth = input.bitWidth := by
  cases op <;> rfl

@[simp] lemma outputBitWidth_eq_shape {kind : ProblemKind}
    {input output : CShape} {pre post : RuntimeCtx kind}
    (op : ClassicalOp input output pre post) :
    op.outputBitWidth = output.bitWidth := by
  cases op <;> rfl

@[simp] lemma inputBitWidth_bit {kind : ProblemKind}
    (opcode : Resource.BitOpcode) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx opcode.inputShape)
    (outputRef : CWriteRef ctx opcode.outputShape) :
    (ClassicalOp.bit opcode ctx inputRef outputRef).inputBitWidth =
      opcode.inputShape.bitWidth :=
  rfl

lemma outputBitWidth_bit {kind : ProblemKind}
    (opcode : Resource.BitOpcode) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx opcode.inputShape)
    (outputRef : CWriteRef ctx opcode.outputShape) :
    (ClassicalOp.bit opcode ctx inputRef outputRef).outputBitWidth = 1 :=
  by
    cases opcode <;> rfl

@[simp] lemma inputBitWidth_wordUnary {kind : ProblemKind}
    (opcode : Resource.WordUnaryOpcode) (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.wordUnary opcode width ctx inputRef outputRef).inputBitWidth = width :=
  rfl

@[simp] lemma outputBitWidth_wordUnary {kind : ProblemKind}
    (opcode : Resource.WordUnaryOpcode) (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.wordUnary opcode width ctx inputRef outputRef).outputBitWidth = width :=
  rfl

@[simp] lemma inputBitWidth_wordBinary {kind : ProblemKind}
    (opcode : Resource.WordBinaryOpcode) (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (opcode.outputShape width)) :
    (ClassicalOp.wordBinary opcode width ctx inputRef outputRef).inputBitWidth =
      width + width :=
  rfl

@[simp] lemma outputBitWidth_wordBinary {kind : ProblemKind}
    (opcode : Resource.WordBinaryOpcode) (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (opcode.outputShape width)) :
    (ClassicalOp.wordBinary opcode width ctx inputRef outputRef).outputBitWidth =
      (opcode.outputShape width).bitWidth :=
  rfl

@[simp] lemma inputBitWidth_wordResize {kind : ProblemKind}
    (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord sourceWidth))
    (outputRef : CWriteRef ctx (.unsignedWord targetWidth)) :
    (ClassicalOp.wordResize sourceWidth targetWidth ctx inputRef
      outputRef).inputBitWidth = sourceWidth :=
  rfl

@[simp] lemma outputBitWidth_wordResize {kind : ProblemKind}
    (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord sourceWidth))
    (outputRef : CWriteRef ctx (.unsignedWord targetWidth)) :
    (ClassicalOp.wordResize sourceWidth targetWidth ctx inputRef
      outputRef).outputBitWidth = targetWidth :=
  rfl

@[simp] lemma inputBitWidth_addCarry {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit)) :
    (ClassicalOp.addCarry width ctx inputRef outputRef).inputBitWidth = width + width :=
  rfl

@[simp] lemma outputBitWidth_addCarry {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit)) :
    (ClassicalOp.addCarry width ctx inputRef outputRef).outputBitWidth = width + 1 :=
  rfl

@[simp] lemma inputBitWidth_subBorrow {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit)) :
    (ClassicalOp.subBorrow width ctx inputRef outputRef).inputBitWidth = width + width :=
  rfl

@[simp] lemma outputBitWidth_subBorrow {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit)) :
    (ClassicalOp.subBorrow width ctx inputRef outputRef).outputBitWidth = width + 1 :=
  rfl

@[simp] lemma inputBitWidth_mulFull {kind : ProblemKind}
    (leftWidth rightWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth)))
    (outputRef : CWriteRef ctx (.unsignedWord (leftWidth + rightWidth))) :
    (ClassicalOp.mulFull leftWidth rightWidth ctx inputRef outputRef).inputBitWidth =
      leftWidth + rightWidth :=
  rfl

@[simp] lemma outputBitWidth_mulFull {kind : ProblemKind}
    (leftWidth rightWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth)))
    (outputRef : CWriteRef ctx (.unsignedWord (leftWidth + rightWidth))) :
    (ClassicalOp.mulFull leftWidth rightWidth ctx inputRef outputRef).outputBitWidth =
      leftWidth + rightWidth :=
  rfl

@[simp] lemma inputBitWidth_divRem {kind : ProblemKind}
    (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (outputRef : CWriteRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))) :
    (ClassicalOp.divRem numeratorWidth divisorWidth ctx inputRef outputRef).inputBitWidth =
      numeratorWidth + divisorWidth :=
  rfl

@[simp] lemma outputBitWidth_divRem {kind : ProblemKind}
    (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (outputRef : CWriteRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))) :
    (ClassicalOp.divRem numeratorWidth divisorWidth ctx inputRef outputRef).outputBitWidth =
      numeratorWidth + divisorWidth :=
  rfl

@[simp] lemma inputBitWidth_packProduct {kind : ProblemKind}
    {left right : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product left right))
    (outputRef : CWriteRef ctx (.product left right)) :
    (ClassicalOp.packProduct ctx inputRef outputRef).inputBitWidth =
      left.bitWidth + right.bitWidth :=
  rfl

@[simp] lemma outputBitWidth_packProduct {kind : ProblemKind}
    {left right : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product left right))
    (outputRef : CWriteRef ctx (.product left right)) :
    (ClassicalOp.packProduct ctx inputRef outputRef).outputBitWidth =
      left.bitWidth + right.bitWidth :=
  rfl

@[simp] lemma inputBitWidth_packBoundedSignedWord {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.boundedSignedWord width)) :
    (ClassicalOp.packBoundedSignedWord width ctx inputRef
      outputRef).inputBitWidth = width :=
  rfl

@[simp] lemma outputBitWidth_packBoundedSignedWord {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.boundedSignedWord width)) :
    (ClassicalOp.packBoundedSignedWord width ctx inputRef
      outputRef).outputBitWidth = width :=
  rfl

@[simp] lemma inputBitWidth_packOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product .bit payload))
    (outputRef : CWriteRef ctx (.option payload)) :
    (ClassicalOp.packOption ctx inputRef outputRef).inputBitWidth =
      1 + payload.bitWidth :=
  rfl

@[simp] lemma outputBitWidth_packOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product .bit payload))
    (outputRef : CWriteRef ctx (.option payload)) :
    (ClassicalOp.packOption ctx inputRef outputRef).outputBitWidth =
      1 + payload.bitWidth :=
  rfl

@[simp] lemma inputBitWidth_unpackOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.option payload))
    (outputRef : CWriteRef ctx (.product .bit payload)) :
    (ClassicalOp.unpackOption ctx inputRef outputRef).inputBitWidth =
      1 + payload.bitWidth :=
  rfl

@[simp] lemma outputBitWidth_unpackOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.option payload))
    (outputRef : CWriteRef ctx (.product .bit payload)) :
    (ClassicalOp.unpackOption ctx inputRef outputRef).outputBitWidth =
      1 + payload.bitWidth :=
  rfl

@[simp] lemma inputBitWidth_unpackUnitResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unitResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackUnitResidue width ctx inputRef
      outputRef).inputBitWidth = width :=
  rfl

@[simp] lemma outputBitWidth_unpackUnitResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unitResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackUnitResidue width ctx inputRef
      outputRef).outputBitWidth = width :=
  rfl

@[simp] lemma inputBitWidth_unpackCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.canonicalResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackCanonicalResidue width ctx inputRef
      outputRef).inputBitWidth = width :=
  rfl

@[simp] lemma outputBitWidth_unpackCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.canonicalResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width)) :
    (ClassicalOp.unpackCanonicalResidue width ctx inputRef
      outputRef).outputBitWidth = width :=
  rfl

@[simp] lemma inputBitWidth_packCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.canonicalResidue width)) :
    (ClassicalOp.packCanonicalResidue width ctx inputRef
      outputRef).inputBitWidth = width :=
  rfl

@[simp] lemma outputBitWidth_packCanonicalResidue {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.canonicalResidue width)) :
    (ClassicalOp.packCanonicalResidue width ctx inputRef
      outputRef).outputBitWidth = width :=
  rfl

@[simp] lemma inputBitWidth_unpackEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.ellipticCurvePoint width))
    (outputRef : CWriteRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))) :
    (ClassicalOp.unpackEllipticCurvePoint width ctx inputRef
      outputRef).inputBitWidth = 1 + 2 * width :=
  rfl

lemma outputBitWidth_unpackEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.ellipticCurvePoint width))
    (outputRef : CWriteRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))) :
    (ClassicalOp.unpackEllipticCurvePoint width ctx inputRef
      outputRef).outputBitWidth = 1 + 2 * width :=
  by
    change 1 + (width + width) = 1 + 2 * width
    omega

lemma inputBitWidth_packEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (outputRef : CWriteRef ctx (.ellipticCurvePoint width)) :
    (ClassicalOp.packEllipticCurvePoint width ctx inputRef
      outputRef).inputBitWidth = 1 + 2 * width :=
  by
    change 1 + (width + width) = 1 + 2 * width
    omega

@[simp] lemma outputBitWidth_packEllipticCurvePoint {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (outputRef : CWriteRef ctx (.ellipticCurvePoint width)) :
    (ClassicalOp.packEllipticCurvePoint width ctx inputRef
      outputRef).outputBitWidth = 1 + 2 * width :=
  rfl

@[simp] lemma inputBitWidth_vectorRead {kind : ProblemKind}
    (length elementWidth : Nat) (index : Fin length) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx (.unsignedWord elementWidth)) :
    (ClassicalOp.vectorRead length elementWidth index ctx inputRef
      outputRef).inputBitWidth = length * elementWidth :=
  rfl

@[simp] lemma outputBitWidth_vectorRead {kind : ProblemKind}
    (length elementWidth : Nat) (index : Fin length) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx (.unsignedWord elementWidth)) :
    (ClassicalOp.vectorRead length elementWidth index ctx inputRef
      outputRef).outputBitWidth = elementWidth :=
  rfl

@[simp] lemma inputBitWidth_vectorWrite {kind : ProblemKind}
    (length elementWidth : Nat) (index : Fin length) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.fixedVector length (.unsignedWord elementWidth))
        (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx
      (.fixedVector length (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorWrite length elementWidth index ctx inputRef
      outputRef).inputBitWidth = length * elementWidth + elementWidth :=
  rfl

@[simp] lemma outputBitWidth_vectorWrite {kind : ProblemKind}
    (length elementWidth : Nat) (index : Fin length) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.fixedVector length (.unsignedWord elementWidth))
        (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx
      (.fixedVector length (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorWrite length elementWidth index ctx inputRef
      outputRef).outputBitWidth = length * elementWidth :=
  rfl

@[simp] lemma inputBitWidth_vectorSwap {kind : ProblemKind}
    (length elementWidth : Nat) (left right : Fin length) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx
      (.fixedVector length (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorSwap length elementWidth left right ctx inputRef
      outputRef).inputBitWidth = length * elementWidth :=
  rfl

@[simp] lemma outputBitWidth_vectorSwap {kind : ProblemKind}
    (length elementWidth : Nat) (left right : Fin length) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx
      (.fixedVector length (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorSwap length elementWidth left right ctx inputRef
      outputRef).outputBitWidth = length * elementWidth :=
  rfl

@[simp] lemma inputBitWidth_vectorRowXor {kind : ProblemKind}
    (length elementWidth : Nat) (source destination : Fin length)
    (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx
      (.fixedVector length (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorRowXor length elementWidth source destination ctx inputRef
      outputRef).inputBitWidth = length * elementWidth :=
  rfl

@[simp] lemma outputBitWidth_vectorRowXor {kind : ProblemKind}
    (length elementWidth : Nat) (source destination : Fin length)
    (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.fixedVector length (.unsignedWord elementWidth)))
    (outputRef : CWriteRef ctx
      (.fixedVector length (.unsignedWord elementWidth))) :
    (ClassicalOp.vectorRowXor length elementWidth source destination ctx inputRef
      outputRef).outputBitWidth = length * elementWidth :=
  rfl

/-- Resizing has the declared modulo-two-to-the-target-width semantics. -/
lemma eval_wordResize_toNat {kind : ProblemKind}
    (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord sourceWidth))
    (outputRef : CWriteRef ctx (.unsignedWord targetWidth))
    (input : CShape.Word sourceWidth) :
    ((ClassicalOp.wordResize sourceWidth targetWidth ctx inputRef outputRef).eval
      input).toNat = input.toNat % CShape.wordModulus targetWidth :=
  rfl

/-- A resize is lossless whenever the represented value fits the target width. -/
lemma eval_wordResize_exact {kind : ProblemKind}
    (sourceWidth targetWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord sourceWidth))
    (outputRef : CWriteRef ctx (.unsignedWord targetWidth))
    (input : CShape.Word sourceWidth)
    (inputFits : input.toNat < CShape.wordModulus targetWidth) :
    ((ClassicalOp.wordResize sourceWidth targetWidth ctx inputRef outputRef).eval
      input).toNat = input.toNat := by
  rw [eval_wordResize_toNat, Nat.mod_eq_of_lt inputFits]

/-- Product packing preserves both values, their order, and all nesting. -/
lemma eval_packProduct_eq {kind : ProblemKind}
    {left right : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product left right))
    (outputRef : CWriteRef ctx (.product left right))
    (input : CShape.Value (.product left right)) :
    (ClassicalOp.packProduct ctx inputRef outputRef).eval input = input :=
  rfl

/-- Bounded-signed packing changes only the nominal shape. -/
lemma eval_packBoundedSignedWord_encoding {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.boundedSignedWord width))
    (input : CShape.Word width) :
    ((ClassicalOp.packBoundedSignedWord width ctx inputRef outputRef).eval
      input).boundedSignedEncoding.val = input.toNat := by
  cases input
  rfl

/-- A false tag produces the empty optional encoding. -/
lemma eval_packOption_false {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product .bit payload))
    (outputRef : CWriteRef ctx (.option payload))
    (value : CShape.Value payload) :
    (ClassicalOp.packOption ctx inputRef outputRef).eval
        (.product (.bit false) value) = .optionNone :=
  rfl

/-- A true tag retains the supplied optional payload exactly. -/
lemma eval_packOption_true {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.product .bit payload))
    (outputRef : CWriteRef ctx (.option payload))
    (value : CShape.Value payload) :
    (ClassicalOp.packOption ctx inputRef outputRef).eval
        (.product (.bit true) value) = .optionSome value :=
  rfl

/-- Unpacking an empty option returns a false tag and initialized payload. -/
lemma eval_unpackOption_none {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.option payload))
    (outputRef : CWriteRef ctx (.product .bit payload)) :
    (ClassicalOp.unpackOption ctx inputRef outputRef).eval
        (.optionNone : CShape.Value (.option payload)) =
      .product (.bit false) (CShape.initialValue payload) :=
  rfl

/-- Unpacking a present option preserves its true tag and exact payload. -/
lemma eval_unpackOption_some {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.option payload))
    (outputRef : CWriteRef ctx (.product .bit payload))
    (value : CShape.Value payload) :
    (ClassicalOp.unpackOption ctx inputRef outputRef).eval
        (.optionSome value) = .product (.bit true) value :=
  rfl

/-- Repacking a typed unpacked option returns its exact original encoding. -/
lemma eval_packOption_unpackOption {kind : ProblemKind}
    {payload : CShape} (ctx : RuntimeCtx kind)
    (unpackInput : CInputRef ctx (.option payload))
    (unpackOutput : CWriteRef ctx (.product .bit payload))
    (packInput : CInputRef ctx (.product .bit payload))
    (packOutput : CWriteRef ctx (.option payload))
    (input : CShape.Value (.option payload)) :
    (ClassicalOp.packOption ctx packInput packOutput).eval
        ((ClassicalOp.unpackOption ctx unpackInput unpackOutput).eval input) = input := by
  cases input <;> rfl

/-- Unit-residue unpacking exposes exactly the stored raw word encoding. -/
lemma eval_unpackUnitResidue_toNat {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unitResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width))
    (input : CShape.Value (.unitResidue width)) :
    ((ClassicalOp.unpackUnitResidue width ctx inputRef outputRef).eval
      input).toNat = input.unitResidueEncoding.val := by
  cases input
  rfl

/-- Unpacking exposes exactly the stored raw residue encoding. -/
lemma eval_unpackCanonicalResidue_toNat {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.canonicalResidue width))
    (outputRef : CWriteRef ctx (.unsignedWord width))
    (input : CShape.Value (.canonicalResidue width)) :
    ((ClassicalOp.unpackCanonicalResidue width ctx inputRef outputRef).eval
      input).toNat = input.residueEncoding.val := by
  cases input
  rfl

/-- Packing preserves a word's raw encoding without asserting modulus validity. -/
lemma eval_packCanonicalResidue_encoding {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.unsignedWord width))
    (outputRef : CWriteRef ctx (.canonicalResidue width))
    (input : CShape.Word width) :
    ((ClassicalOp.packCanonicalResidue width ctx inputRef outputRef).eval
      input).residueEncoding.val = input.toNat := by
  cases input
  rfl

/-- Point unpacking preserves the exact raw tag and coordinate encoding. -/
lemma eval_unpackEllipticCurvePoint_roundTrip {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx (.ellipticCurvePoint width))
    (outputRef : CWriteRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (input : CShape.Value (.ellipticCurvePoint width)) :
    CShape.packEllipticCurvePoint width
      ((ClassicalOp.unpackEllipticCurvePoint width ctx inputRef outputRef).eval input) =
        input := by
  exact CShape.packEllipticCurvePoint_unpackEllipticCurvePoint width input

/-- Point packing preserves the exact raw tag and coordinate encoding. -/
lemma eval_packEllipticCurvePoint_roundTrip {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width))))
    (outputRef : CWriteRef ctx (.ellipticCurvePoint width))
    (input : CShape.Value
      (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))) :
    CShape.unpackEllipticCurvePoint width
      ((ClassicalOp.packEllipticCurvePoint width ctx inputRef outputRef).eval input) =
        input := by
  exact CShape.unpackEllipticCurvePoint_packEllipticCurvePoint width input

lemma eval_addCarry_low {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit))
    (input : CShape.Value
      (.product (.unsignedWord width) (.unsignedWord width))) :
    ((ClassicalOp.addCarry width ctx inputRef outputRef).eval input).first.toNat =
      (input.first.toNat + input.second.toNat) % CShape.wordModulus width :=
  by
    cases input
    rfl

lemma eval_addCarry_flag {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit))
    (input : CShape.Value
      (.product (.unsignedWord width) (.unsignedWord width))) :
    ((ClassicalOp.addCarry width ctx inputRef outputRef).eval input).second.toBool =
      decide (CShape.wordModulus width ≤ input.first.toNat + input.second.toNat) :=
  by
    cases input
    rfl

lemma eval_subBorrow_low {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit))
    (input : CShape.Value
      (.product (.unsignedWord width) (.unsignedWord width))) :
    ((ClassicalOp.subBorrow width ctx inputRef outputRef).eval input).first =
      CShape.wordSub width input.first input.second :=
  by
    cases input
    rfl

lemma eval_subBorrow_flag {kind : ProblemKind}
    (width : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord width) (.unsignedWord width)))
    (outputRef : CWriteRef ctx (.product (.unsignedWord width) .bit))
    (input : CShape.Value
      (.product (.unsignedWord width) (.unsignedWord width))) :
    ((ClassicalOp.subBorrow width ctx inputRef outputRef).eval input).second.toBool =
      decide (input.first.toNat < input.second.toNat) :=
  by
    cases input
    rfl

lemma eval_mulFull_val {kind : ProblemKind}
    (leftWidth rightWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth)))
    (outputRef : CWriteRef ctx (.unsignedWord (leftWidth + rightWidth)))
    (input : CShape.Value
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth))) :
    ((ClassicalOp.mulFull leftWidth rightWidth ctx inputRef outputRef).eval
      input).toNat =
      (input.first.toNat * input.second.toNat) %
        CShape.wordModulus (leftWidth + rightWidth) :=
  by
    cases input
    rfl

/-- The full-width multiplication carrier is large enough for the exact product. -/
lemma mulFull_product_lt (leftWidth rightWidth : Nat)
    (input : CShape.Value
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth))) :
    input.first.toNat * input.second.toNat <
      CShape.wordModulus (leftWidth + rightWidth) := by
  rw [CShape.wordModulus, pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt input.first.toNat_lt input.second.toNat_lt

/-- Full multiplication does not truncate its mathematical product. -/
lemma eval_mulFull_exact {kind : ProblemKind}
    (leftWidth rightWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth)))
    (outputRef : CWriteRef ctx (.unsignedWord (leftWidth + rightWidth)))
    (input : CShape.Value
      (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth))) :
    ((ClassicalOp.mulFull leftWidth rightWidth ctx inputRef outputRef).eval
      input).toNat = input.first.toNat * input.second.toNat := by
  rw [eval_mulFull_val, Nat.mod_eq_of_lt (mulFull_product_lt _ _ input)]

lemma eval_divRem_quotient {kind : ProblemKind}
    (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (outputRef : CWriteRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (input : CShape.Value
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))) :
    ((ClassicalOp.divRem numeratorWidth divisorWidth ctx inputRef outputRef).eval
      input).first.toNat =
      (input.first.toNat / input.second.toNat) % CShape.wordModulus numeratorWidth :=
  by
    cases input
    rfl

lemma eval_divRem_remainder {kind : ProblemKind}
    (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (outputRef : CWriteRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (input : CShape.Value
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))) :
    ((ClassicalOp.divRem numeratorWidth divisorWidth ctx inputRef outputRef).eval
      input).second.toNat =
      (input.first.toNat % input.second.toNat) % CShape.wordModulus divisorWidth :=
  by
    cases input
    rfl

/-- The quotient encoding is exact (and in range) for every machine input. -/
lemma eval_divRem_quotient_exact {kind : ProblemKind}
    (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (outputRef : CWriteRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (input : CShape.Value
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))) :
    ((ClassicalOp.divRem numeratorWidth divisorWidth ctx inputRef outputRef).eval
      input).first.toNat = input.first.toNat / input.second.toNat := by
  rw [eval_divRem_quotient, Nat.mod_eq_of_lt]
  exact (Nat.div_le_self _ _).trans_lt input.first.toNat_lt

/-- Under the public nonzero-divisor condition, the remainder encoding is exact. -/
lemma eval_divRem_remainder_exact {kind : ProblemKind}
    (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (outputRef : CWriteRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (input : CShape.Value
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (divisor_ne_zero : input.second.toNat ≠ 0) :
    ((ClassicalOp.divRem numeratorWidth divisorWidth ctx inputRef outputRef).eval
      input).second.toNat = input.first.toNat % input.second.toNat := by
  rw [eval_divRem_remainder, Nat.mod_eq_of_lt]
  exact (Nat.mod_lt _ (Nat.pos_of_ne_zero divisor_ne_zero)).trans input.second.toNat_lt

/-- Valid division results reconstruct the input numerator exactly. -/
lemma eval_divRem_reconstruct {kind : ProblemKind}
    (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (outputRef : CWriteRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (input : CShape.Value
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (divisor_ne_zero : input.second.toNat ≠ 0) :
    let result :=
      (ClassicalOp.divRem numeratorWidth divisorWidth ctx inputRef outputRef).eval input
    result.first.toNat * input.second.toNat + result.second.toNat = input.first.toNat := by
  dsimp only
  rw [eval_divRem_quotient_exact,
    eval_divRem_remainder_exact _ _ _ _ _ _ divisor_ne_zero]
  simpa [Nat.mul_comm] using Nat.div_add_mod input.first.toNat input.second.toNat

/-- A valid division result's remainder is strictly smaller than the divisor. -/
lemma eval_divRem_remainder_lt {kind : ProblemKind}
    (numeratorWidth divisorWidth : Nat) (ctx : RuntimeCtx kind)
    (inputRef : CInputRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (outputRef : CWriteRef ctx
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (input : CShape.Value
      (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth)))
    (divisor_ne_zero : input.second.toNat ≠ 0) :
    ((ClassicalOp.divRem numeratorWidth divisorWidth ctx inputRef outputRef).eval
      input).second.toNat < input.second.toNat := by
  rw [eval_divRem_remainder_exact _ _ _ _ _ _ divisor_ne_zero]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero divisor_ne_zero)

end ClassicalOp

namespace ClassicalOpFixtures

private def operationCtx {kind : ProblemKind}
    (input output : CShape) : RuntimeCtx kind :=
  let withInput : RuntimeCtx kind :=
    RuntimeCtx.addBorrowedInput (kind := kind) RuntimeCtx.empty
      ⟨0⟩ input (by simp [RuntimeCtx.keys])
  RuntimeCtx.addWorkspace (kind := kind) withInput ⟨1⟩ output (by
    change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
    decide)

private def operationInputRef {kind : ProblemKind}
    (input output : CShape) : CStorageRef (operationCtx input output : RuntimeCtx kind) input where
  key := ⟨0⟩
  role := .borrowedInput
  slot := .there .here

private def operationOutputRef {kind : ProblemKind}
    (input output : CShape) : CWriteRef (operationCtx input output : RuntimeCtx kind) output where
  key := ⟨1⟩
  role := .workspace
  slot := .here
  writable := by decide

private def word4 (value : Nat) : CShape.Word 4 :=
  CShape.wordOfNat 4 value

private def words3x2 : CShape.Value
    (.fixedVector 3 (.unsignedWord 2)) :=
  .fixedVector fun index => CShape.wordOfNat 2 index.val

private def xorCtx : RuntimeCtx .classical :=
  operationCtx (.product .bit .bit) .bit

private def xorOp := ClassicalOp.bit .xor xorCtx
  (.storage (operationInputRef (.product .bit .bit) .bit))
  (operationOutputRef (.product .bit .bit) .bit)

private def add4Ctx : RuntimeCtx .classical :=
  operationCtx
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit)

private def add4 := ClassicalOp.addCarry 4 add4Ctx
  (.storage (operationInputRef
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit)))
  (operationOutputRef
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit))

private def mulCtx : RuntimeCtx .classical :=
  operationCtx
    (.product (.unsignedWord 3) (.unsignedWord 5))
    (.unsignedWord 8)

private def mul := ClassicalOp.mulFull 3 5 mulCtx
  (.storage (operationInputRef
    (.product (.unsignedWord 3) (.unsignedWord 5))
    (.unsignedWord 8)))
  (operationOutputRef
    (.product (.unsignedWord 3) (.unsignedWord 5))
    (.unsignedWord 8))

private def divCtx : RuntimeCtx .classical :=
  operationCtx
    (.product (.unsignedWord 6) (.unsignedWord 3))
    (.product (.unsignedWord 6) (.unsignedWord 3))

private def divide := ClassicalOp.divRem 6 3 divCtx
  (.storage (operationInputRef
    (.product (.unsignedWord 6) (.unsignedWord 3))
    (.product (.unsignedWord 6) (.unsignedWord 3))))
  (operationOutputRef
    (.product (.unsignedWord 6) (.unsignedWord 3))
    (.product (.unsignedWord 6) (.unsignedWord 3)))

private def swapCtx : RuntimeCtx .classical :=
  operationCtx
    (.fixedVector 3 (.unsignedWord 2))
    (.fixedVector 3 (.unsignedWord 2))

private def swap := ClassicalOp.vectorSwap 3 2
  ⟨0, by decide⟩ ⟨2, by decide⟩ swapCtx
  (.storage (operationInputRef
    (.fixedVector 3 (.unsignedWord 2))
    (.fixedVector 3 (.unsignedWord 2))))
  (operationOutputRef
    (.fixedVector 3 (.unsignedWord 2))
    (.fixedVector 3 (.unsignedWord 2)))

/-- Representative bit evaluation is shape-correct by construction. -/
example : (xorOp.eval (.product (.bit true) (.bit false))).toBool = true := rfl

/-- Carry is emitted by the same instruction that computes the low word. -/
example : (add4.eval (.product (word4 15) (word4 1))).first.toNat = 0 := by decide
example : (add4.eval (.product (word4 15) (word4 1))).second.toBool = true := by
  decide

/-- Full multiplication fixes the sum of operand widths as its output width. -/
example : (mul.eval
    (.product (CShape.wordOfNat 3 7) (CShape.wordOfNat 5 3))).toNat = 21 := by
  decide

/-- Division and remainder share one input and one closed instruction event. -/
example : (divide.eval
    (.product (CShape.wordOfNat 6 37) (CShape.wordOfNat 3 5))).first.toNat = 7 := by
  decide
example : (divide.eval
    (.product (CShape.wordOfNat 6 37) (CShape.wordOfNat 3 5))).second.toNat = 2 := by
  decide

/-- Representative vector operations use statically valid indices. -/
example : ((swap.eval words3x2).get ⟨0, by decide⟩).toNat = 2 := by
  decide

/-- The typed instruction retains its declared bit/word coordinate. -/
example : add4.label = .addCarry 4 := rfl

example : add4.flow.peakResidentSpace = add4Ctx.residentSpace := by simp

/-- Operand and writable-result shapes are genuinely present in the context;
the local flow therefore cannot report an empty detached footprint. -/
example : add4.flow.peakResidentSpace .classicalBits = 13 := by decide
example : add4.flow.peakAuxiliarySpace .classicalBits = 5 := by decide

/-- Classical placement retains the same operation in a quantum context. -/
private def qAddCtx : RuntimeCtx .quantum :=
  operationCtx
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit)

private def qAdd := ClassicalOp.addCarry 4 qAddCtx
  (.storage (operationInputRef
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit)))
  (operationOutputRef
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit))

private def borrowedWordCtx : RuntimeCtx .classical :=
  RuntimeCtx.addBorrowedInput (kind := .classical) RuntimeCtx.empty
    ⟨0⟩ (.unsignedWord 4) (by simp [RuntimeCtx.keys])

example : qAdd.label = .addCarry 4 := rfl

/-!
The following importer-visible compile-time fixtures pin the construction
boundary.  Each attempted escape fails in Lean rather than by convention.
-/

/-- error: Application type mismatch -/
#guard_msgs(error, drop info, substring := true) in
#check xorOp.eval (CShape.wordOfNat 1 0)

/-- error: Type mismatch -/
#guard_msgs(error, drop info, substring := true) in
example : CShape.Value (.unsignedWord 4) :=
  xorOp.eval (.product (.bit false) (.bit true))

/-- error: Type mismatch -/
#guard_msgs(error, drop info, substring := true) in
example : ClassicalOp
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit) add4Ctx swapCtx :=
  add4

/-- error: Application type mismatch -/
#guard_msgs(error, drop info, substring := true) in
#check swap.eval (CShape.wordOfNat 2 1)

/-- error: Type mismatch -/
#guard_msgs(error, drop info, substring := true) in
example (value : CShape.Value (.unsignedWord 4)) :
    CShape.Value (.boundedSignedWord 4) := value

/-- error: Type mismatch -/
#guard_msgs(error, drop info, substring := true) in
example (value : CShape.Value (.unsignedWord 4)) :
    CShape.Value (.canonicalResidue 4) := value

/-- error: Type mismatch -/
#guard_msgs(error, drop info, substring := true) in
example (value : CShape.Value (.canonicalResidue 4)) :
    CShape.Value (.unitResidue 4) := value

/-- error: Type mismatch -/
#guard_msgs(error, drop info, substring := true) in
example (value : CShape.Value (.bits 3)) :
    CShape.Value (.fixedVector 3 .bit) := value

/-- error: unsolved goals -/
#guard_msgs(error, drop info, substring := true) in
example : CStorageRef (RuntimeCtx.empty : RuntimeCtx .classical)
    (.unsignedWord 4) where
  key := ⟨0⟩
  role := .workspace
  slot := by simp

/-- error: Tactic `decide` proved that the proposition -/
#guard_msgs(error, drop info, substring := true) in
example : CWriteRef borrowedWordCtx (.unsignedWord 4) where
  key := ⟨0⟩
  role := .borrowedInput
  slot := .here
  writable := by decide

/-- error: Application type mismatch -/
#guard_msgs(error, drop info, substring := true) in
#check ClassicalOp.addCarry 4 add4Ctx
  (.storage (operationOutputRef
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit)).toCStorageRef)
  (operationOutputRef
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit))

/-- error: Application type mismatch -/
#guard_msgs(error, drop info, substring := true) in
#check ClassicalOp.addCarry 4 (RuntimeCtx.empty : RuntimeCtx .classical)
  (.storage (operationInputRef
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit)))
  (operationOutputRef
    (.product (.unsignedWord 4) (.unsignedWord 4))
    (.product (.unsignedWord 4) .bit))

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.named

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.mk

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.ofFunction

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.callback

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.withEvent

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.withCost

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.withFootprint

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.withFlow

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.gate

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.preparation

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.measurement

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.quantumSubroutine

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.depth

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.qubitSpace

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.randomBits

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.residue

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.point

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
#check ClassicalOp.recovery

end ClassicalOpFixtures

end QuantumAlg

end
