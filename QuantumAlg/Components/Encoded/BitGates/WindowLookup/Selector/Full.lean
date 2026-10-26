/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Resources

/-!
# Complete static address trees as the all-retained pruning case

These equalities connect the exact native recursion with closed complete-tree
counts, without evaluating a large concrete address tree in a consumer.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorTrie

noncomputable section

private lemma compactFork_full (remaining : Nat) :
    compactFork (full remaining) (full remaining) = full (remaining + 1) := by
  cases remaining <;> rfl

/-- Retaining every original leaf gives exactly the complete actual static tree. -/
lemma pruneAt_true (width remaining offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    pruneAt width (fun _ => true) remaining offset bounded = full remaining := by
  induction remaining generalizing offset with
  | zero => rfl
  | succ remaining ih =>
      simp only [pruneAt, ih, compactFork_full]

/-- The whole original address interval has no skipped callback when every row is retained. -/
lemma prune_true (width : Nat) : prune width (fun _ => true) = full width :=
  pruneAt_true width width 0 (by omega)

/-- An identical cost at every retained leaf is charged with its exact multiplicity. -/
lemma leafSumAt_const {width remaining : Nat} (tree : SelectorTrie remaining)
    (cost offset : Nat) (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    leafSumAt width (fun _ => cost) tree offset bounded = tree.leaves * cost := by
  induction tree generalizing offset with
  | skip remaining => simp only [leafSumAt, leaves, Nat.zero_mul]
  | leaf => simp only [leafSumAt, leaves, Nat.one_mul]
  | @fork remaining left right leftIH rightIH =>
      dsimp only [leafSumAt, leaves]
      rw [leftIH, rightIH, Nat.add_mul]

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorTrie
