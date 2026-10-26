/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Pruning
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.SelectedAction

/-!
# Exact full-width address labels and finite pruning support

The decoder follows every original most-significant-first address bit. Static
right subtrees advance by the exact remaining binary interval size. Pruning
selects a callback precisely when the original full-width predicate is true.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Decode the original full-width address by its exact successive binary intervals. -/
def addressLabelAt (frame : SelectorFrame encoding width) :
    (remaining : Nat) → (depth : Nat) → depth + remaining = width →
      (offset : Nat) → offset + 2 ^ remaining ≤ 2 ^ width → Data → Fin (2 ^ width)
  | 0, _, _, offset, bounded, _ =>
      ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩
  | remaining + 1, depth, fits, offset, bounded, state =>
      if (frame.addressAt depth (by omega)).get state then
        frame.addressLabelAt remaining (depth + 1) (by omega)
          (offset + 2 ^ remaining) (right_bound bounded) state
      else frame.addressLabelAt remaining (depth + 1) (by omega)
        offset (left_bound bounded) state

/-- Whether the original address reaches an actual retained static callback. -/
def containsAt (frame : SelectorFrame encoding width) :
    {remaining : Nat} → SelectorTrie remaining →
      (depth : Nat) → depth + remaining = width → Data → Bool
  | _, .skip _, _, _, _ => false
  | _, .leaf, _, _, _ => true
  | _, .fork left right, depth, fits, state =>
      if (frame.addressAt depth (by omega)).get state then
        frame.containsAt right (depth + 1) (by omega) state
      else frame.containsAt left (depth + 1) (by omega) state

/-- Exactly the retained full-width leaf acts, including address zero when it is present. -/
lemma selectedActionAt_eq (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Data → Data) {remaining : Nat} (tree : SelectorTrie remaining)
    (depth : Nat) (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data) :
    frame.selectedActionAt action tree depth fits offset bounded state =
      if frame.containsAt tree depth fits state then
        action (frame.addressLabelAt remaining depth fits offset bounded state) state
      else state := by
  induction tree generalizing depth offset with
  | skip remaining => rfl
  | leaf => rfl
  | @fork remaining left right leftIH rightIH =>
      dsimp only [selectedActionAt, containsAt, addressLabelAt]
      split
      · exact rightIH _ (by omega) _ (right_bound bounded)
      · exact leftIH _ (by omega) _ (left_bound bounded)

private lemma containsAt_compactFork (frame : SelectorFrame encoding width)
    {remaining : Nat} (left right : SelectorTrie remaining) (depth : Nat)
    (fits : depth + (remaining + 1) = width) (state : Data) :
    frame.containsAt (SelectorTrie.compactFork left right) depth fits state =
      if (frame.addressAt depth (by omega)).get state then
        frame.containsAt right (depth + 1) (by omega) state
      else frame.containsAt left (depth + 1) (by omega) state := by
  cases left <;> cases right <;> simp only [SelectorTrie.compactFork, containsAt, ite_self]

/-- Static pruning matches the predicate of the original full-width decoded address. -/
lemma containsAt_pruneAt (frame : SelectorFrame encoding width)
    (active : Fin (2 ^ width) → Bool) (remaining depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data) :
    frame.containsAt (SelectorTrie.pruneAt width active remaining offset bounded) depth fits state =
      active (frame.addressLabelAt remaining depth fits offset bounded state) := by
  induction remaining generalizing depth offset with
  | zero =>
      simp only [SelectorTrie.pruneAt, addressLabelAt]
      split <;> simp_all only [containsAt, Bool.not_eq_true]
  | succ remaining ih =>
      rw [SelectorTrie.pruneAt, frame.containsAt_compactFork]
      dsimp only [addressLabelAt]
      split
      · exact ih _ (by omega) _ (right_bound bounded)
      · exact ih _ (by omega) _ (left_bound bounded)

/-- The concrete pruned selector never truncates or identifies distinct original addresses. -/
lemma selectedActionAt_prune (frame : SelectorFrame encoding width)
    (active : Fin (2 ^ width) → Bool) (action : Fin (2 ^ width) → Data → Data) (state : Data) :
    frame.selectedActionAt action (SelectorTrie.prune width active)
      0 (by omega) 0 (by omega) state =
      if active (frame.addressLabelAt width 0 (by omega) 0 (by omega) state) then
        action (frame.addressLabelAt width 0 (by omega) 0 (by omega) state) state else state := by
  rw [frame.selectedActionAt_eq, SelectorTrie.prune, frame.containsAt_pruneAt]

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
