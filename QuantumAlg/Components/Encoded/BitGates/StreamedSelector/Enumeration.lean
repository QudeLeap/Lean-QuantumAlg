/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Pruning
import Mathlib.Data.List.Range

/-!
# Ordered physical leaves of a pruned stream

This list records the actual static callbacks, including callbacks whose
runtime selection bit is false. Pruning below a fixed limit leaves precisely
the original increasing physical indices and introduces no runtime code
generation or permutation of their actions.
-/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open WindowLookup

/-- Every physically present callback in unchanged depth-first order. -/
def labelsAt {width : Nat} : {remaining : Nat} → SelectorTrie remaining →
    (offset : Nat) → offset + 2 ^ remaining ≤ 2 ^ width → List (Fin (2 ^ width))
  | _, .skip _, _, _ => []
  | 0, .leaf, offset, bounded =>
      [⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩]
  | remaining + 1, .fork left right, offset, bounded =>
      labelsAt left offset (SelectorFrame.left_bound bounded) ++
        labelsAt right (offset + 2 ^ remaining) (SelectorFrame.right_bound bounded)

/-- All callback labels stay within the original exact binary interval. -/
lemma labelsAt_bounds {width remaining : Nat} (tree : SelectorTrie remaining)
    (offset : Nat) (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (label : Fin (2 ^ width)) (present : label ∈ labelsAt tree offset bounded) :
    offset ≤ label.val ∧ label.val < offset + 2 ^ remaining := by
  induction tree generalizing offset with
  | skip remaining => simp [labelsAt] at present
  | leaf =>
      simp only [labelsAt, List.mem_singleton] at present
      subst label
      simp
  | @fork remaining left right leftIH rightIH =>
      simp only [labelsAt, List.mem_append] at present
      rcases present with first | second
      · have localBounds := leftIH offset (SelectorFrame.left_bound bounded) first
        rw [pow_succ]
        omega
      · have localBounds := rightIH (offset + 2 ^ remaining)
          (SelectorFrame.right_bound bounded) second
        rw [pow_succ]
        omega

private lemma labelsAt_compactFork {width remaining : Nat}
    (left right : SelectorTrie remaining) (offset : Nat)
    (bounded : offset + 2 ^ (remaining + 1) ≤ 2 ^ width) :
    labelsAt (SelectorTrie.compactFork left right) offset bounded =
      labelsAt left offset (SelectorFrame.left_bound bounded) ++
        labelsAt right (offset + 2 ^ remaining) (SelectorFrame.right_bound bounded) := by
  cases left <;> cases right <;> rfl

/-- Removing absent leaves preserves exactly the increasing retained source positions. -/
lemma labelsAt_pruneBelow {width : Nat} (limit remaining offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    (labelsAt (SelectorTrie.pruneAt width (fun label => decide (label.val < limit))
      remaining offset bounded) offset bounded).map Fin.val =
        (List.range' offset (2 ^ remaining)).filter (fun label => decide (label < limit)) := by
  induction remaining generalizing offset with
  | zero =>
      simp only [SelectorTrie.pruneAt, pow_zero]
      split <;> simp_all [labelsAt]
  | succ remaining ih =>
      rw [SelectorTrie.pruneAt, labelsAt_compactFork, List.map_append, ih, ih]
      rw [pow_succ, Nat.mul_two, ← List.range'_append_1, List.filter_append]

end

end QuantumAlg.EncodedBit.StreamedSelector
