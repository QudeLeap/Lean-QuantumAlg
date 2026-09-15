/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.FinPow
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact word split and wire placement for HRS recursion

The low word has ceiling-half width and the high word floor-half width.
The inactive high word can supply the carry's internal borrowing, and the
low word can supply the controlled incrementer's borrowed word
[HRS16, paper.tex:232-260]. The final wire is the one external dirty bit.
The source big-endian order is high/low/dirty; the shared bridge order is
low/high/dirty. This module proves the corresponding exact word and wire maps.
-/

namespace QuantumAlg.MAU.Addition.HRS

/-- Width of the low recursive word. -/
def lowWidth (width : Nat) : Nat := (width + 1) / 2

/-- Width of the high recursive word. -/
def highWidth (width : Nat) : Nat := width / 2

/-- The two recursive words partition the original word exactly. -/
theorem hrsSplit_width_sum (width : Nat) : lowWidth width + highWidth width = width := by
  unfold lowWidth highWidth
  omega

/-- Both internal borrowing requirements hold for the chosen split. -/
theorem hrsSplit_capacity (width : Nat) :
    lowWidth width - 2 ≤ highWidth width ∧ highWidth width ≤ lowWidth width ∧
      lowWidth width ≤ highWidth width + 1 := by
  unfold lowWidth highWidth
  omega

/-- Both recursive calls strictly decrease the input width above the base cases. -/
theorem hrsSplit_decreases (width : Nat) (h : 2 ≤ width) :
    lowWidth width < width ∧ highWidth width < width := by
  unfold lowWidth highWidth
  omega

/-- Exact split into low and high words, without padding. -/
def splitWord (width : Nat) :
    Fin (2 ^ width) ≃ Fin (2 ^ lowWidth width) × Fin (2 ^ highWidth width) :=
  (finCongr (congrArg (fun value : Nat => 2 ^ value)
      (by have := hrsSplit_width_sum width
          omega : width = highWidth width + lowWidth width))).trans
    ((prodEquiv (m := highWidth width) (n := lowWidth width)).symm.trans (Equiv.prodComm _ _))

/-- Reassemble the same low and high words into the original-width carrier. -/
def joinWord (width : Nat)
    (words : Fin (2 ^ lowWidth width) × Fin (2 ^ highWidth width)) : Fin (2 ^ width) :=
  (splitWord width).symm words

theorem hrsSplit_low_value (width : Nat) (word : Fin (2 ^ width)) :
    ((splitWord width) word).1.val = word.val % 2 ^ lowWidth width := rfl

theorem hrsSplit_high_value (width : Nat) (word : Fin (2 ^ width)) :
    ((splitWord width) word).2.val = word.val / 2 ^ lowWidth width := rfl

/-- Joining uses the actual low-word modulus, not a padded block size. -/
theorem hrsJoin_value (width : Nat)
    (words : Fin (2 ^ lowWidth width) × Fin (2 ^ highWidth width)) :
    (joinWord width words).val = words.1.val + 2 ^ lowWidth width * words.2.val := rfl

theorem hrsJoin_split (width : Nat) (word : Fin (2 ^ width)) :
    joinWord width ((splitWord width) word) = word :=
  (splitWord width).symm_apply_apply word

theorem hrsSplit_join (width : Nat)
    (words : Fin (2 ^ lowWidth width) × Fin (2 ^ highWidth width)) :
    splitWord width (joinWord width words) = words :=
  (splitWord width).apply_symm_apply words

/-- Parenthesis changes preserve the exact big-endian basis label. -/
theorem hrsProdEquiv_assoc {a b c : Nat}
    (x : Fin (2 ^ a)) (y : Fin (2 ^ b)) (z : Fin (2 ^ c)) :
    finCongr (congrArg (fun value : Nat => 2 ^ value) (Nat.add_assoc a b c))
        (prodEquiv (m := a + b) (n := c) (prodEquiv (x, y), z)) =
      prodEquiv (m := a) (n := b + c) (x, prodEquiv (y, z)) := by
  apply Fin.ext
  change z.val + 2 ^ c * (y.val + 2 ^ b * x.val) =
    (z.val + 2 ^ c * y.val) + 2 ^ (b + c) * x.val
  rw [pow_add]
  ring

/-- Map physical high/low/dirty order to low/high/dirty order. -/
def splitWire (width wire : Nat) : Nat :=
  if wire < highWidth width then lowWidth width + wire
  else if wire < width then wire - highWidth width else wire

/-- Inverse physical wire map; all positions outside the input word are fixed. -/
def joinWire (width wire : Nat) : Nat :=
  if wire < lowWidth width then highWidth width + wire
  else if wire < width then wire - lowWidth width else wire

theorem hrsSplitWire_left_inverse (width wire : Nat) :
    joinWire width (splitWire width wire) = wire := by
  have hsum := hrsSplit_width_sum width
  unfold splitWire joinWire
  split_ifs <;> omega

theorem hrsSplitWire_right_inverse (width wire : Nat) :
    splitWire width (joinWire width wire) = wire := by
  have hsum := hrsSplit_width_sum width
  unfold splitWire joinWire
  split_ifs <;> omega

/-- Physical relabeling is a permutation, with no duplicated work wires. -/
theorem hrsSplitWire_injective (width : Nat) : Function.Injective (splitWire width) := by
  intro a b h
  have h' := congrArg (joinWire width) h
  simpa only [hrsSplitWire_left_inverse] using h'

theorem hrsJoinWire_injective (width : Nat) : Function.Injective (joinWire width) := by
  intro a b h
  have h' := congrArg (splitWire width) h
  simpa only [hrsSplitWire_right_inverse] using h'

/-- The physical split stays within the original word and its one dirty bit. -/
theorem hrsSplitWire_lt (width wire : Nat) (h : wire < width + 1) :
    splitWire width wire < width + 1 := by
  have hsum := hrsSplit_width_sum width
  unfold splitWire
  split_ifs <;> omega

theorem hrsJoinWire_lt (width wire : Nat) (h : wire < width + 1) :
    joinWire width wire < width + 1 := by
  have hsum := hrsSplit_width_sum width
  unfold joinWire
  split_ifs <;> omega

/-- Splitting never moves the sole external dirty bit. -/
theorem hrsSplitWire_dirty (width : Nat) : splitWire width width = width := by
  have hsum := hrsSplit_width_sum width
  simp only [splitWire]
  split_ifs <;> omega

end QuantumAlg.MAU.Addition.HRS
