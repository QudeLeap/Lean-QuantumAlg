/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Actual control and two-word coordinates for a register swap

The control and both supplied words occupy their original physical wires.
The product encoding introduces no auxiliary systems, including at width zero.
-/

namespace QuantumAlg.EncodedRegisterSwap

noncomputable section

open BinaryLabelEncoding

abbrev Data (width : Nat) := Bool × (Fin (2 ^ width) × Fin (2 ^ width))

def wordsEncoding (width : Nat) := prod (finIdentity width) (finIdentity width)

def encoding (width : Nat) : BinaryLabelEncoding (Data width) :=
  prod bool (wordsEncoding width)

def control (width : Nat) : EncodedBit (encoding width) :=
  prodLeftBit bool (wordsEncoding width) boolBit

def leftBit (width : Nat) (index : Fin width) : EncodedBit (encoding width) :=
  prodRightBit bool (wordsEncoding width)
    (prodLeftBit (finIdentity width) (finIdentity width) (finIdentityBit width index))

def rightBit (width : Nat) (index : Fin width) : EncodedBit (encoding width) :=
  prodRightBit bool (wordsEncoding width)
    (prodRightBit (finIdentity width) (finIdentity width) (finIdentityBit width index))

def leftWord (width : Nat) : EncodedBit.Word (encoding width) width := ⟨leftBit width⟩

def rightWord (width : Nat) : EncodedBit.Word (encoding width) width := ⟨rightBit width⟩

lemma control_get (width : Nat) (state : Data width) :
    (control width).get state = state.1 := rfl

lemma leftBit_get (width : Nat) (index : Fin width) (state : Data width) :
    (leftBit width index).get state = (finIdentityBit width index).get state.2.1 := rfl

lemma rightBit_get (width : Nat) (index : Fin width) (state : Data width) :
    (rightBit width index).get state = (finIdentityBit width index).get state.2.2 := rfl

lemma control_left_ne (width : Nat) (index : Fin width) :
    (control width).wire ≠ (leftBit width index).wire := by
  intro same
  have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
  change 0 = 1 + index.val at values
  omega

lemma control_right_ne (width : Nat) (index : Fin width) :
    (control width).wire ≠ (rightBit width index).wire := by
  intro same
  have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
  change 0 = 1 + (width + index.val) at values
  omega

lemma left_right_ne (width : Nat) (left right : Fin width) :
    (leftBit width left).wire ≠ (rightBit width right).wire := by
  intro same
  have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
  change 1 + left.val = 1 + (width + right.val) at values
  omega

lemma left_injective (width : Nat) :
    Function.Injective (fun index => (leftBit width index).wire) := by
  intro left right same
  have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
  change 1 + left.val = 1 + right.val at values
  exact Fin.ext (by omega)

lemma right_injective (width : Nat) :
    Function.Injective (fun index => (rightBit width index).wire) := by
  intro left right same
  have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
  change 1 + (width + left.val) = 1 + (width + right.val) at values
  exact Fin.ext (by omega)

/-- Equality of every actual wire readout identifies the entire original word. -/
lemma label_eq_of_bits {width : Nat} {left right : Fin (2 ^ width)}
    (same : ∀ index, (finIdentityBit width index).get left =
      (finIdentityBit width index).get right) : left = right := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  have actual := same (WireAddress.littleEndianWire bit)
  change left.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val =
    right.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val at actual
  simpa only [WireAddress.bitIndex_littleEndianWire] using actual

end

end QuantumAlg.EncodedRegisterSwap
