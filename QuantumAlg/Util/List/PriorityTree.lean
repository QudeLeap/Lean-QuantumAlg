/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.List.Basic

/-!
# Priority search through complete static subword zero predicates

The ordered first marked leaf is specified independently by List.find?.
At a fork, a complete zero predicate on the higher-priority subtree
selects the lower subtree; otherwise the first marked leaf lies in
the higher subtree. These are pure mathematical identities, not
unaccounted circuit instructions or a quantum resource claim.
-/

namespace QuantumAlg.ListPriority

/-- A static finite priority tree, with higher-priority leaves preceding lower-priority leaves. -/
inductive Tree (Label : Type*) where
  | empty
  | leaf (label : Label)
  | fork (higher lower : Tree Label)

namespace Tree

variable {Label : Type*}

/-- Every original label occurs in its declared priority order. -/
def leaves : Tree Label → List Label
  | .empty => []
  | .leaf label => [label]
  | .fork higher lower => higher.leaves ++ lower.leaves

/-- Binary priority evaluation retains the first marked original label or the empty result. -/
def first (marked : Label → Bool) : Tree Label → Option Label
  | .empty => none
  | .leaf label => if marked label then some label else none
  | .fork higher lower =>
      match higher.first marked with
      | none => lower.first marked
      | some label => some label

/-- The tree result agrees with an independent ordered list search. -/
lemma first_eq_find (tree : Tree Label) (marked : Label → Bool) :
    tree.first marked = tree.leaves.find? marked := by
  induction tree with
  | empty => rfl
  | leaf label =>
      by_cases selected : marked label = true <;> simp [first, leaves, selected]
  | fork higher lower higherCorrect lowerCorrect =>
      simp only [first, leaves, List.find?_append, higherCorrect, lowerCorrect]
      cases higher.leaves.find? marked <;> rfl

/-- A complete subword zero predicate inspects all original leaves of that subtree. -/
def allZero (tree : Tree Label) (marked : Label → Bool) : Bool :=
  !tree.leaves.any marked

/-- No marked original leaf is exactly the complete zero predicate. -/
lemma first_eq_none_iff (tree : Tree Label) (marked : Label → Bool) :
    tree.first marked = none ↔ tree.allZero marked = true := by
  rw [first_eq_find]
  simp [allZero, List.find?_eq_none]

/-- The actual fork selection criterion can use the full higher-subword zero predicate. -/
lemma first_fork (higher lower : Tree Label) (marked : Label → Bool) :
    (Tree.fork higher lower).first marked =
      if higher.allZero marked then lower.first marked else higher.first marked := by
  cases selected : higher.first marked with
  | none =>
      have zero := (higher.first_eq_none_iff marked).mp selected
      simp only [first, selected, zero, if_true]
  | some label =>
      have nonzero : ¬higher.allZero marked = true := by
        intro zero
        have absent := (higher.first_eq_none_iff marked).mpr zero
        rw [selected] at absent
        cases absent
      simp only [first, selected, if_neg nonzero]

end Tree

end QuantumAlg.ListPriority
