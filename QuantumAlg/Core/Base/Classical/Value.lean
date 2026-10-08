/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Shape

/-!
# Values in classical storage

The value carrier depends only on storage shapes. It does not select a native
instruction language, grant oracle access, or attach a cost to a mathematical
function on these values. Operation declarations and actual placed execution
use this same carrier independently of their chosen language.
-/

namespace QuantumAlg.CShape

/-- Nominal runtime encodings carried by the closed storage shapes.

Every constructor fixes its `CShape` index, so equal-width unsigned, signed,
residue, unit-residue, bit-vector, and fixed-vector values remain distinct
types.  Residue and elliptic-curve constructors are raw encodings only: their
modulus, unit, curve, and validity proofs belong to later semantic carriers. -/
public inductive Value : CShape → Type where
  | unit : Value .unit
  | bit (value : Bool) : Value .bit
  | finite {cardinality : ℕ+} (value : Fin cardinality) :
      Value (.finite cardinality)
  | bits {count : Nat} (get : Fin count → Bool) : Value (.bits count)
  | unsignedWord {width : Nat} (value : Fin (2 ^ width)) :
      Value (.unsignedWord width)
  | boundedSignedWord {width : Nat} (encoding : Fin (2 ^ width)) :
      Value (.boundedSignedWord width)
  | optionNone {payload : CShape} : Value (.option payload)
  | optionSome {payload : CShape} (value : Value payload) : Value (.option payload)
  | product {left right : CShape} (first : Value left) (second : Value right) :
      Value (.product left right)
  | fixedVector {length : Nat} {element : CShape}
      (get : Fin length → Value element) : Value (.fixedVector length element)
  | canonicalResidue {modulusWidth : Nat} (encoding : Fin (2 ^ modulusWidth)) :
      Value (.canonicalResidue modulusWidth)
  | unitResidue {modulusWidth : Nat} (encoding : Fin (2 ^ modulusWidth)) :
      Value (.unitResidue modulusWidth)
  | ellipticCurvePoint {fieldWidth : Nat} (infinityTag : Bool)
      (x y : Fin (2 ^ fieldWidth)) : Value (.ellipticCurvePoint fieldWidth)


end QuantumAlg.CShape
