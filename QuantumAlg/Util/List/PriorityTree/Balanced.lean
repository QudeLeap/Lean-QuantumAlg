/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.List.PriorityTree.Height
import Mathlib.Data.List.TakeDrop

/-!
# Static balanced priority trees with complete original ordered leaves

The supplied depth bounds the real prefix stack. Whenever the original
list fits its power-of-two capacity, the balanced tree retains exactly
that complete ordered list, including the empty and singleton cases.
This static construction is not an executed priority instruction.
-/

namespace QuantumAlg.ListPriority.Tree

variable {Label : Type*}

/-- Divide the original priority list into consecutive balanced static halves. -/
def balanced : Nat → List Label → Tree Label
  | _, [] => .empty
  | _, [label] => .leaf label
  | 0, label :: _ => .leaf label
  | depth + 1, first :: second :: rest =>
      let labels := first :: second :: rest
      .fork (balanced depth (labels.take ((labels.length + 1) / 2)))
        (balanced depth (labels.drop ((labels.length + 1) / 2)))

/-- The complete original priority list is present, with no dropped or duplicated leaf. -/
lemma balanced_leaves (depth : Nat) (labels : List Label) (fits : labels.length ≤ 2 ^ depth) :
    (balanced depth labels).leaves = labels := by
  induction depth generalizing labels with
  | zero =>
      cases labels with
      | nil => rfl
      | cons label rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              simp only [List.length_cons, Nat.pow_zero] at fits
              omega
  | succ depth ih =>
      cases labels with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              let labels := first :: second :: rest
              have capacity : labels.length ≤ 2 ^ depth * 2 := by
                simpa only [Nat.pow_succ] using fits
              have higherFits : (labels.take ((labels.length + 1) / 2)).length ≤ 2 ^ depth := by
                rw [List.length_take]
                apply Nat.le_trans (Nat.min_le_left _ _)
                omega
              have lowerFits : (labels.drop ((labels.length + 1) / 2)).length ≤ 2 ^ depth := by
                rw [List.length_drop]
                omega
              exact (congrArg₂ List.append (ih _ higherFits) (ih _ lowerFits)).trans
                (List.take_append_drop _ labels)

/-- The actual static tree requires no more than the supplied number of prefix levels. -/
lemma balanced_height_le (depth : Nat) (labels : List Label) :
    (balanced depth labels).height ≤ depth := by
  induction depth generalizing labels with
  | zero =>
      cases labels with
      | nil => exact Nat.le_refl _
      | cons label rest => cases rest <;> exact Nat.le_refl _
  | succ depth ih =>
      cases labels with
      | nil => exact Nat.zero_le _
      | cons first rest =>
          cases rest with
          | nil => exact Nat.zero_le _
          | cons second rest =>
              exact Nat.add_le_add_right (Nat.max_le_of_le_of_le (ih _) (ih _)) 1

end QuantumAlg.ListPriority.Tree
