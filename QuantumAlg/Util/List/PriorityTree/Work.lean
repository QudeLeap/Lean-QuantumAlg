/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.List.PriorityTree.Balanced
import Mathlib.Tactic.Linarith

/-!
# Independent work bounds of complete balanced priority trees

Each fork tests its complete higher-priority subword twice. These pure
counts retain every fork and every tested original source position.
-/

namespace QuantumAlg.ListPriority.Tree

variable {Label : Type*}

/-- Number of actual binary forks in the static priority tree. -/
def forks : Tree Label → Nat
  | .empty => 0
  | .leaf _ => 0
  | .fork higher lower => higher.forks + lower.forks + 1

/-- Sum of complete higher-priority subword lengths over every actual fork. -/
def testVolume : Tree Label → Nat
  | .empty => 0
  | .leaf _ => 0
  | .fork higher lower => higher.leaves.length + higher.testVolume + lower.testVolume

/-- Complete subword tests have at most one original occurrence per tree level. -/
lemma testVolume_le (tree : Tree Label) : tree.testVolume ≤ tree.leaves.length * tree.height := by
  induction tree with
  | empty => exact Nat.le_refl _
  | leaf _ => exact Nat.le_refl _
  | fork higher lower higherBound lowerBound =>
      have higherHeight := Nat.le_max_left higher.height lower.height
      have lowerHeight := Nat.le_max_right higher.height lower.height
      have higherWork := Nat.mul_le_mul_left higher.leaves.length higherHeight
      have lowerWork := Nat.mul_le_mul_left lower.leaves.length lowerHeight
      simp only [testVolume, leaves, List.length_append, height]
      nlinarith

/-- Compact balancing has no padded empty forks, including the empty and singleton cases. -/
lemma balanced_forks_le (depth : Nat) (labels : List Label) :
    (balanced depth labels).forks ≤ labels.length - 1 := by
  induction depth generalizing labels with
  | zero =>
      cases labels with
      | nil => exact Nat.le_refl _
      | cons label rest => cases rest <;> exact Nat.zero_le _
  | succ depth ih =>
      cases labels with
      | nil => exact Nat.le_refl _
      | cons first rest =>
          cases rest with
          | nil => exact Nat.le_refl _
          | cons second rest =>
              let labels := first :: second :: rest
              have higher := ih (labels.take ((labels.length + 1) / 2))
              have lower := ih (labels.drop ((labels.length + 1) / 2))
              have positive : 2 ≤ labels.length := by simp only [labels, List.length_cons]; omega
              rw [List.length_take] at higher
              rw [List.length_drop] at lower
              change (balanced depth (labels.take ((labels.length + 1) / 2))).forks +
                (balanced depth (labels.drop ((labels.length + 1) / 2))).forks + 1 ≤
                  labels.length - 1
              omega

/-- Balanced tests inspect at most the complete original length times the supplied height. -/
lemma balanced_testVolume_le (depth : Nat) (labels : List Label)
    (capacity : labels.length ≤ 2 ^ depth) :
    (balanced depth labels).testVolume ≤ labels.length * depth := by
  have actual := testVolume_le (balanced depth labels)
  rw [balanced_leaves depth labels capacity] at actual
  exact Nat.le_trans actual
    (Nat.mul_le_mul_left labels.length (balanced_height_le depth labels))

end QuantumAlg.ListPriority.Tree
