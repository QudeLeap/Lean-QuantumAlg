/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor

/-!
# Binary-label bit and word encodings

This focused module is re-exported by `QuantumAlg.Components.EncodedBitGates`.
-/

section

namespace QuantumAlg

noncomputable section

namespace BinaryLabelEncoding

/-- The single Boolean bit stored by the canonical Boolean encoding. -/
def boolBit : EncodedBit bool where
  wire := ⟨0, by decide⟩
  get := id
  flip := fun b => !b
  get_eq := by
    intro b
    cases b <;> decide
  encode_flip := by
    intro b
    cases b <;> decide

/-! ### Exact-layout bit lenses -/

/-- Bit lens induced by an exact binary-register layout equivalence.  This is
the safe way to expose individual wires for raw label spaces where every
bit-flip is still a semantic label. -/
def ofEquivBit {Data : Type} {n : Nat} (layout : Data ≃ Fin (2 ^ n))
    (wire : Fin n) : EncodedBit (ofEquiv layout) where
  wire := wire
  get := fun x => (layout x).val.testBit (WireAddress.bitIndex wire).val
  flip := fun x => layout.symm (WireAddress.flipBit wire (layout x))
  get_eq := by
    intro x
    rfl
  encode_flip := by
    intro x
    simp [ofEquiv]

/-- Bit lens for the raw identity encoding of an `n`-qubit basis-label space. -/
def finIdentityBit (n : Nat) (wire : Fin n) :
    EncodedBit (finIdentity n) :=
  ofEquivBit (Equiv.refl (Fin (2 ^ n))) wire

/-- Word lens for the raw identity encoding of an `n`-qubit basis-label space. -/
def finIdentityWord (n : Nat) : EncodedBit.Word (finIdentity n) n where
  bit := finIdentityBit n

/-! ### Product-encoding bit readout helpers -/

/-- Wire of a bit inherited from the left component of a product encoding. -/
def prodLeftWire {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (wire : Fin left.width) :
    Fin (prod left right).width :=
  ⟨wire.val, by
    change wire.val < left.width + right.width
    omega⟩

/-- Wire of a bit inherited from the right component of a product encoding. -/
def prodRightWire {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (wire : Fin right.width) :
    Fin (prod left right).width :=
  ⟨left.width + wire.val, by
    change left.width + wire.val < left.width + right.width
    omega⟩

@[simp] theorem prodLeftWire_val {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin left.width) :
    (prodLeftWire left right wire).val = wire.val :=
  rfl

@[simp] theorem prodRightWire_val {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin right.width) :
    (prodRightWire left right wire).val = left.width + wire.val :=
  rfl

theorem bitIndex_prodLeftWire {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin left.width) :
    (WireAddress.bitIndex (prodLeftWire left right wire)).val =
      right.width + (WireAddress.bitIndex wire).val := by
  dsimp [WireAddress.bitIndex, prodLeftWire]
  omega

theorem bitIndex_prodRightWire {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin right.width) :
    (WireAddress.bitIndex (prodRightWire left right wire)).val =
      (WireAddress.bitIndex wire).val := by
  dsimp [WireAddress.bitIndex, prodRightWire]
  omega

/-- Bit readout inherited from the left component of a product encoding. -/
theorem prodLeft_get_eq {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (bit : EncodedBit left) (x : Left × Right) :
    ((prod left right).encode x).val.testBit
        (WireAddress.bitIndex (prodLeftWire left right bit.wire)).val =
      bit.get x.1 := by
  rw [bitIndex_prodLeftWire]
  change
    (prodEquiv (m := left.width) (n := right.width)
        (left.encode x.1, right.encode x.2)).val.testBit
        (right.width + (WireAddress.bitIndex bit.wire).val) =
      bit.get x.1
  rw [prodEquiv_testBit_left]
  exact bit.get_eq x.1

/-- Bit readout inherited from the right component of a product encoding. -/
theorem prodRight_get_eq {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (bit : EncodedBit right) (x : Left × Right) :
    ((prod left right).encode x).val.testBit
        (WireAddress.bitIndex (prodRightWire left right bit.wire)).val =
      bit.get x.2 := by
  rw [bitIndex_prodRightWire]
  change
    (prodEquiv (m := left.width) (n := right.width)
        (left.encode x.1, right.encode x.2)).val.testBit
        (WireAddress.bitIndex bit.wire).val =
      bit.get x.2
  rw [prodEquiv_testBit_right]
  exact bit.get_eq x.2

/-- Flipping a left-component wire is the same as flipping its corresponding
wire in the product encoding. -/
theorem prodEquiv_flip_left {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin left.width) (leftLabel : Fin (2 ^ left.width))
    (rightLabel : Fin (2 ^ right.width)) :
    prodEquiv (m := left.width) (n := right.width)
        (WireAddress.flipBit wire leftLabel, rightLabel) =
      WireAddress.flipBit (prodLeftWire left right wire)
        (prodEquiv (m := left.width) (n := right.width)
          (leftLabel, rightLabel)) := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hiWidth : i < left.width + right.width
  · by_cases hlow : i < right.width
    · let bit : Fin right.width := ⟨i, hlow⟩
      have hleft :=
        prodEquiv_testBit_right
          (left := WireAddress.flipBit wire leftLabel) (right := rightLabel) bit
      have hbase :=
        prodEquiv_testBit_right (left := leftLabel) (right := rightLabel) bit
      have hne :
          ¬ (WireAddress.bitIndex (prodLeftWire left right wire)).val =
            bit.val := by
        rw [bitIndex_prodLeftWire]
        dsimp [bit]
        omega
      rw [hleft]
      change rightLabel.val.testBit bit.val =
        ((prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel)).val ^^^
          2 ^ (WireAddress.bitIndex
            (prodLeftWire left right wire)).val).testBit bit.val
      rw [Nat.testBit_xor, Nat.testBit_two_pow, hbase]
      have hdec :
          decide ((WireAddress.bitIndex (prodLeftWire left right wire)).val =
            bit.val) = false := by
        rw [decide_eq_false_iff_not]
        exact hne
      rw [hdec]
      simp
    · push Not at hlow
      let bit : Fin left.width := ⟨i - right.width, by omega⟩
      have hidx : right.width + bit.val = i := by
        dsimp [bit]
        omega
      have hleft :=
        prodEquiv_testBit_left
          (left := WireAddress.flipBit wire leftLabel)
          (right := rightLabel) bit
      have hbase :=
        prodEquiv_testBit_left (left := leftLabel) (right := rightLabel) bit
      rw [← hidx, hleft]
      change (leftLabel.val ^^^ 2 ^ (WireAddress.bitIndex wire).val).testBit
          bit.val =
        ((prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel)).val ^^^
          2 ^ (WireAddress.bitIndex
            (prodLeftWire left right wire)).val).testBit
          (right.width + bit.val)
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      rw [hbase]
      congr 1
      rw [decide_eq_decide, bitIndex_prodLeftWire]
      omega
  · push Not at hiWidth
    have hleftLt :
        (prodEquiv (m := left.width) (n := right.width)
          (WireAddress.flipBit wire leftLabel, rightLabel)).val < 2 ^ i :=
      lt_of_lt_of_le
        (prodEquiv (m := left.width) (n := right.width)
          (WireAddress.flipBit wire leftLabel, rightLabel)).isLt
        (Nat.pow_le_pow_right (by norm_num) hiWidth)
    have hrightLt :
        (WireAddress.flipBit (prodLeftWire left right wire)
          (prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel))).val < 2 ^ i :=
      lt_of_lt_of_le
        (WireAddress.flipBit (prodLeftWire left right wire)
          (prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel))).isLt
        (Nat.pow_le_pow_right (by norm_num) hiWidth)
    rw [Nat.testBit_lt_two_pow hleftLt, Nat.testBit_lt_two_pow hrightLt]

/-- Flipping a right-component wire is the same as flipping its corresponding
wire in the product encoding. -/
theorem prodEquiv_flip_right {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (wire : Fin right.width) (leftLabel : Fin (2 ^ left.width))
    (rightLabel : Fin (2 ^ right.width)) :
    prodEquiv (m := left.width) (n := right.width)
        (leftLabel, WireAddress.flipBit wire rightLabel) =
      WireAddress.flipBit (prodRightWire left right wire)
        (prodEquiv (m := left.width) (n := right.width)
          (leftLabel, rightLabel)) := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hiWidth : i < left.width + right.width
  · by_cases hlow : i < right.width
    · let bit : Fin right.width := ⟨i, hlow⟩
      have hleft :=
        prodEquiv_testBit_right (left := leftLabel)
          (right := WireAddress.flipBit wire rightLabel) bit
      have hbase :=
        prodEquiv_testBit_right (left := leftLabel) (right := rightLabel) bit
      rw [hleft]
      change (rightLabel.val ^^^ 2 ^ (WireAddress.bitIndex wire).val).testBit
          bit.val =
        ((prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel)).val ^^^
          2 ^ (WireAddress.bitIndex
            (prodRightWire left right wire)).val).testBit bit.val
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      rw [hbase]
      congr 1
      rw [decide_eq_decide, bitIndex_prodRightWire]
    · push Not at hlow
      let bit : Fin left.width := ⟨i - right.width, by omega⟩
      have hidx : right.width + bit.val = i := by
        dsimp [bit]
        omega
      have hleft :=
        prodEquiv_testBit_left (left := leftLabel)
          (right := WireAddress.flipBit wire rightLabel) bit
      have hbase :=
        prodEquiv_testBit_left (left := leftLabel) (right := rightLabel) bit
      have hne :
          ¬ (WireAddress.bitIndex (prodRightWire left right wire)).val =
            right.width + bit.val := by
        rw [bitIndex_prodRightWire]
        omega
      rw [← hidx, hleft]
      change leftLabel.val.testBit bit.val =
        ((prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel)).val ^^^
          2 ^ (WireAddress.bitIndex
            (prodRightWire left right wire)).val).testBit
          (right.width + bit.val)
      rw [Nat.testBit_xor, Nat.testBit_two_pow, hbase]
      have hdec :
          decide ((WireAddress.bitIndex (prodRightWire left right wire)).val =
            right.width + bit.val) = false := by
        rw [decide_eq_false_iff_not]
        exact hne
      rw [hdec]
      simp
  · push Not at hiWidth
    have hleftLt :
        (prodEquiv (m := left.width) (n := right.width)
          (leftLabel, WireAddress.flipBit wire rightLabel)).val < 2 ^ i :=
      lt_of_lt_of_le
        (prodEquiv (m := left.width) (n := right.width)
          (leftLabel, WireAddress.flipBit wire rightLabel)).isLt
        (Nat.pow_le_pow_right (by norm_num) hiWidth)
    have hrightLt :
        (WireAddress.flipBit (prodRightWire left right wire)
          (prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel))).val < 2 ^ i :=
      lt_of_lt_of_le
        (WireAddress.flipBit (prodRightWire left right wire)
          (prodEquiv (m := left.width) (n := right.width)
            (leftLabel, rightLabel))).isLt
        (Nat.pow_le_pow_right (by norm_num) hiWidth)
    rw [Nat.testBit_lt_two_pow hleftLt, Nat.testBit_lt_two_pow hrightLt]

/-- Lift an encoded bit from the left component to the product encoding. -/
def prodLeftBit {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (bit : EncodedBit left) :
    EncodedBit (prod left right) where
  wire := prodLeftWire left right bit.wire
  get := fun x => bit.get x.1
  flip := fun x => (bit.flip x.1, x.2)
  get_eq := by
    intro x
    exact prodLeft_get_eq left right bit x
  encode_flip := by
    intro x
    simp only [prod_encode]
    rw [bit.encode_flip x.1]
    exact prodEquiv_flip_left left right bit.wire (left.encode x.1)
      (right.encode x.2)

/-- Lift an encoded bit from the right component to the product encoding. -/
def prodRightBit {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (bit : EncodedBit right) :
    EncodedBit (prod left right) where
  wire := prodRightWire left right bit.wire
  get := fun x => bit.get x.2
  flip := fun x => (x.1, bit.flip x.2)
  get_eq := by
    intro x
    exact prodRight_get_eq left right bit x
  encode_flip := by
    intro x
    simp only [prod_encode]
    rw [bit.encode_flip x.2]
    exact prodEquiv_flip_right left right bit.wire (left.encode x.1)
      (right.encode x.2)

end BinaryLabelEncoding

end

end QuantumAlg

end
