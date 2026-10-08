/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Components.Gates.Swap.Label
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.FinPow
public import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Fin

/-!
# Symmetric swaps and reversal of binary labels

The original outer-wire invariant proves that the complete sequence of
symmetric swaps reverses exactly the significant bits. This label action
is independent of the execution model and gate accounting.
-/

namespace QuantumAlg

noncomputable section

/-- Left wire of the `index`th symmetric bit-reversal swap. -/
def qftSwapLeft (n : Nat) (index : Fin (n / 2)) : Fin n :=
  ⟨index.val, lt_of_lt_of_le index.isLt (Nat.div_le_self n 2)⟩

/-- Right wire of the `index`th symmetric bit-reversal swap. -/
def qftSwapRight (n : Nat) (index : Fin (n / 2)) : Fin n :=
  ⟨n - 1 - index.val, by
    have hi := index.isLt
    omega⟩

theorem qftSwapLeft_ne_right (n : Nat) (index : Fin (n / 2)) :
    qftSwapLeft n index ≠ qftSwapRight n index := by
  intro h
  have hval := congrArg Fin.val h
  have hi := index.isLt
  simp only [qftSwapLeft, qftSwapRight] at hval
  omega

/-- Basis-label action of the first `count` symmetric swaps. -/
def qftBitReverseLabelPrefix (n : Nat) :
    (count : Nat) → count ≤ n / 2 → Fin (2 ^ n) → Fin (2 ^ n)
  | 0, _, label => label
  | count + 1, hcount, label =>
      let index : Fin (n / 2) := ⟨count, by omega⟩
      qftSwapLabel (qftSwapLeft n index) (qftSwapRight n index)
        (qftBitReverseLabelPrefix n count (by omega) label)

/-- After the first `count` symmetric swaps, the outer `count` wires on each
side contain their reversed source bits and every middle wire is unchanged. -/
theorem qftBitReverseLabelPrefix_invariant (n count : Nat)
    (hcount : count ≤ n / 2) (label : Fin (2 ^ n)) :
    (∀ wire : Fin n, wire.val < count →
      (qftBitReverseLabelPrefix n count hcount label).val.testBit
          (WireAddress.bitIndex wire).val = label.val.testBit wire.val) ∧
    (∀ wire : Fin n, n - count ≤ wire.val →
      (qftBitReverseLabelPrefix n count hcount label).val.testBit
          (WireAddress.bitIndex wire).val = label.val.testBit wire.val) ∧
    (∀ wire : Fin n, count ≤ wire.val → wire.val < n - count →
      (qftBitReverseLabelPrefix n count hcount label).val.testBit
          (WireAddress.bitIndex wire).val =
        label.val.testBit (WireAddress.bitIndex wire).val) := by
  induction count with
  | zero =>
      constructor
      · intro wire hwire
        omega
      constructor
      · intro wire hwire
        omega
      · intro wire hleft hright
        rfl
  | succ count ih =>
      obtain ⟨ihLeft, ihRight, ihMiddle⟩ := ih (by omega)
      let index : Fin (n / 2) := ⟨count, by omega⟩
      let left := qftSwapLeft n index
      let right := qftSwapRight n index
      let previous := qftBitReverseLabelPrefix n count (by omega) label
      have hne : left ≠ right := qftSwapLeft_ne_right n index
      have hnext :
          qftBitReverseLabelPrefix n (count + 1) hcount label =
            qftSwapLabel left right previous := rfl
      constructor
      · intro wire hwire
        rw [hnext]
        by_cases hlt : wire.val < count
        · rw [qftSwapLabel_of_ne left right wire hne]
          · exact ihLeft wire hlt
          · intro heq
            have hval := congrArg Fin.val heq
            simp [left, index, qftSwapLeft] at hval
            omega
          · intro heq
            have hval := congrArg Fin.val heq
            have hi := index.isLt
            simp [right, index, qftSwapRight] at hval
            omega
        · have heq : wire = left := by
            apply Fin.ext
            simp [left, index, qftSwapLeft]
            omega
          subst wire
          rw [qftSwapLabel_left left right hne]
          have hmiddle := ihMiddle right (by
            simp [right, index, qftSwapRight]
            omega) (by
            simp [right, index, qftSwapRight]
            omega)
          have hmirror : n - 1 - (n - 1 - count) = count := by
            have hi := index.isLt
            omega
          have hmiddle' :
              previous.val.testBit count = label.val.testBit count := by
            simpa [previous, right, index, qftSwapRight,
              WireAddress.bitIndex, hmirror] using hmiddle
          have hrightMirror :
              (WireAddress.bitIndex right).val = count := by
            simp [right, index, qftSwapRight, WireAddress.bitIndex]
            have hi := index.isLt
            omega
          rw [hrightMirror]
          simpa [left, index, qftSwapLeft] using hmiddle'
      constructor
      · intro wire hwire
        rw [hnext]
        by_cases houter : n - count ≤ wire.val
        · rw [qftSwapLabel_of_ne left right wire hne]
          · exact ihRight wire houter
          · intro heq
            have hval := congrArg Fin.val heq
            have hi := index.isLt
            simp [left, index, qftSwapLeft] at hval
            omega
          · intro heq
            have hval := congrArg Fin.val heq
            simp [right, index, qftSwapRight] at hval
            omega
        · have heq : wire = right := by
            apply Fin.ext
            simp [right, index, qftSwapRight]
            omega
          subst wire
          rw [qftSwapLabel_right left right hne]
          have hmiddle := ihMiddle left (by
            simp [left, index, qftSwapLeft]) (by
            have hi := index.isLt
            simp [left, index, qftSwapLeft]
            omega)
          simpa [left, right, index, qftSwapLeft, qftSwapRight,
            WireAddress.bitIndex] using hmiddle
      · intro wire hleftBound hrightBound
        rw [hnext, qftSwapLabel_of_ne left right wire hne]
        · exact ihMiddle wire (by omega) (by omega)
        · intro heq
          have hval := congrArg Fin.val heq
          simp [left, index, qftSwapLeft] at hval
          omega
        · intro heq
          have hval := congrArg Fin.val heq
          simp [right, index, qftSwapRight] at hval
          omega

/-- The complete symmetric SWAP network realizes the canonical bit-reversal
permutation on computational-basis labels. -/
theorem qftBitReverseLabel_eq (n : Nat) (label : Fin (2 ^ n)) :
    qftBitReverseLabelPrefix n (n / 2) le_rfl label =
      qftReverseBits n label := by
  apply Fin.val_injective
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · let bit : Fin n := ⟨k, hk⟩
    let wire : Fin n := WireAddress.littleEndianWire bit
    obtain ⟨hleft, hright, hmiddle⟩ :=
      qftBitReverseLabelPrefix_invariant n (n / 2) le_rfl label
    have hindex : WireAddress.bitIndex wire = bit := by
      exact WireAddress.bitIndex_littleEndianWire bit
    have hwireRev : wire = Fin.rev bit := by
      apply Fin.ext
      simp [wire, WireAddress.littleEndianWire, WireAddress.bitIndex, Fin.rev]
      omega
    have hvalue :
        (qftBitReverseLabelPrefix n (n / 2) le_rfl label).val.testBit bit.val =
          label.val.testBit wire.val := by
      by_cases hl : wire.val < n / 2
      · simpa only [hindex] using hleft wire hl
      by_cases hr : n - n / 2 ≤ wire.val
      · simpa only [hindex] using hright wire hr
      · have hm := hmiddle wire (by omega) (by omega)
        have hcentral : bit = wire := by
          apply Fin.ext
          have hb := bit.isLt
          have hw := wire.isLt
          have hv := congrArg Fin.val hindex
          simp [WireAddress.bitIndex] at hv
          omega
        simpa only [hindex, hcentral] using hm
    calc
      (qftBitReverseLabelPrefix n (n / 2) le_rfl label).val.testBit k =
          label.val.testBit wire.val := hvalue
      _ = label.val.testBit (Fin.rev bit).val := by rw [hwireRev]
      _ = (qftReverseBits n label).val.testBit k := by
        symm
        simpa [bit] using qftReverseBits_testBit n label bit
  · have hnk : n ≤ k := by omega
    have hpow : 2 ^ n ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hnk
    rw [Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le
          (qftBitReverseLabelPrefix n (n / 2) le_rfl label).isLt hpow),
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le (qftReverseBits n label).isLt hpow)]

end

end QuantumAlg
