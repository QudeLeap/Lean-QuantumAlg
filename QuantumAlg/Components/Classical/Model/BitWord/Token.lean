/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Built-in width-indexed bit and word operations

Tokens retain the semantic parameters of the existing machine instructions.
Widths are part of the declaration, and vector indices are part of the actual
operation. A word operation is one operation in this declared language; it is
not a claim about a Boolean implementation's gate count or storage.
-/

namespace QuantumAlg.BitWord

/-- Typed operation tokens independent of caller storage placement. -/
public inductive Token : CShape → CShape → Type where
  | randomBits (width : Nat) : Token .unit (.bits width)
  | bit (opcode : Resource.BitOpcode) : Token opcode.inputShape opcode.outputShape
  | wordUnary (opcode : Resource.WordUnaryOpcode) (width : Nat) :
      Token (.unsignedWord width) (.unsignedWord width)
  | wordBinary (opcode : Resource.WordBinaryOpcode) (width : Nat) :
      Token (.product (.unsignedWord width) (.unsignedWord width)) (opcode.outputShape width)
  | wordResize (sourceWidth targetWidth : Nat) :
      Token (.unsignedWord sourceWidth) (.unsignedWord targetWidth)
  | addCarry (width : Nat) :
      Token (.product (.unsignedWord width) (.unsignedWord width))
        (.product (.unsignedWord width) .bit)
  | subBorrow (width : Nat) :
      Token (.product (.unsignedWord width) (.unsignedWord width))
        (.product (.unsignedWord width) .bit)
  | mulFull (leftWidth rightWidth : Nat) :
      Token (.product (.unsignedWord leftWidth) (.unsignedWord rightWidth))
        (.unsignedWord (leftWidth + rightWidth))
  | divRem (numeratorWidth divisorWidth : Nat) :
      Token (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))
        (.product (.unsignedWord numeratorWidth) (.unsignedWord divisorWidth))
  | packFiniteBits (count : Nat) : Token (.fixedVector count (.finite 2)) (.bits count)
  | packProduct (left right : CShape) : Token (.product left right) (.product left right)
  | packBoundedSignedWord (width : Nat) : Token (.unsignedWord width) (.boundedSignedWord width)
  | packOption (payload : CShape) : Token (.product .bit payload) (.option payload)
  | unpackOption (payload : CShape) : Token (.option payload) (.product .bit payload)
  | unpackUnitResidue (width : Nat) : Token (.unitResidue width) (.unsignedWord width)
  | unpackCanonicalResidue (width : Nat) : Token (.canonicalResidue width) (.unsignedWord width)
  | packCanonicalResidue (width : Nat) : Token (.unsignedWord width) (.canonicalResidue width)
  | unpackEllipticCurvePoint (width : Nat) :
      Token (.ellipticCurvePoint width)
        (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))
  | packEllipticCurvePoint (width : Nat) :
      Token (.product .bit (.product (.unsignedWord width) (.unsignedWord width)))
        (.ellipticCurvePoint width)
  | vectorRead (length elementWidth : Nat) (index : Fin length) :
      Token (.fixedVector length (.unsignedWord elementWidth)) (.unsignedWord elementWidth)
  | vectorWrite (length elementWidth : Nat) (index : Fin length) :
      Token (.product (.fixedVector length (.unsignedWord elementWidth))
          (.unsignedWord elementWidth)) (.fixedVector length (.unsignedWord elementWidth))
  | vectorSwap (length elementWidth : Nat) (left right : Fin length) :
      Token (.fixedVector length (.unsignedWord elementWidth))
        (.fixedVector length (.unsignedWord elementWidth))
  | vectorRowXor (length elementWidth : Nat) (source destination : Fin length) :
      Token (.fixedVector length (.unsignedWord elementWidth))
        (.fixedVector length (.unsignedWord elementWidth))

namespace Token

/-- Coordinates preserve the existing width-indexed accounting vocabulary. -/
public def coordinate {input output : CShape} : Token input output → Resource.ClassicalOpLabel
  | .randomBits width => .randomBits width
  | .bit opcode => .bit opcode
  | .wordUnary opcode width => .wordUnary opcode width
  | .wordBinary opcode width => .wordBinary opcode width
  | .wordResize sourceWidth targetWidth => .wordResize sourceWidth targetWidth
  | .addCarry width => .addCarry width
  | .subBorrow width => .subBorrow width
  | .mulFull leftWidth rightWidth => .mulFull leftWidth rightWidth
  | .divRem numeratorWidth divisorWidth => .divRem numeratorWidth divisorWidth
  | .packFiniteBits count => .nominalEncoding (.packFiniteBits count)
  | .packProduct left right => .nominalEncoding (.packProduct left.bitWidth right.bitWidth)
  | .packBoundedSignedWord width => .nominalEncoding (.packBoundedSignedWord width)
  | .packOption payload => .nominalEncoding (.packOption payload.bitWidth)
  | .unpackOption payload => .nominalEncoding (.unpackOption payload.bitWidth)
  | .unpackUnitResidue width => .nominalEncoding (.unpackUnitResidue width)
  | .unpackCanonicalResidue width => .residueEncoding .unpack width
  | .packCanonicalResidue width => .residueEncoding .pack width
  | .unpackEllipticCurvePoint width => .nominalEncoding (.unpackEllipticCurvePoint width)
  | .packEllipticCurvePoint width => .nominalEncoding (.packEllipticCurvePoint width)
  | .vectorRead length width _ => .vector .read length width
  | .vectorWrite length width _ => .vector .write length width
  | .vectorSwap length width _ _ => .vector .swap length width
  | .vectorRowXor length width _ _ => .vector .rowXor length width

end Token

end QuantumAlg.BitWord
