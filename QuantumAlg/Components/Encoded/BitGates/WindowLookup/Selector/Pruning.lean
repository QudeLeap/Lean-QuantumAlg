/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector

/-!
# Static finite leaf pruning without truncating the quantum address

The predicate describes which full-width static leaf programs exist. The
actual selector still reads every address bit and restores all prefixes.
Missing subtrees compile to identity; no runtime address is discarded.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorTrie

noncomputable section

/-- A complete binary address tree has one actual callback at every full-width address. -/
def full : (width : Nat) → SelectorTrie width
  | 0 => .leaf
  | width + 1 => .fork (full width) (full width)

/-- The complete selector has its exact symbolic internal-node count. -/
lemma full_forks (width : Nat) : (full width).forks = 2 ^ width - 1 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [full, forks, ih, pow_succ]
      have positive : 0 < 2 ^ width := Nat.pow_pos (by decide)
      omega

/-- Every full-width address has exactly one actual static leaf callback. -/
lemma full_leaves (width : Nat) : (full width).leaves = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [full, leaves, ih, pow_succ]
      omega

/-- Build a finite subtree from the full-width leaf predicate and exact static interval. -/
def pruneAt (width : Nat) (active : Fin (2 ^ width) → Bool) :
    (remaining : Nat) → (offset : Nat) → offset + 2 ^ remaining ≤ 2 ^ width →
      SelectorTrie remaining
  | 0, offset, bounded =>
      if active ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩ then .leaf
      else .skip 0
  | remaining + 1, offset, bounded =>
      compactFork
        (pruneAt width active remaining offset (SelectorFrame.left_bound bounded))
        (pruneAt width active remaining (offset + 2 ^ remaining)
          (SelectorFrame.right_bound bounded))

/-- Prune only absent static leaves while retaining the original full-width address domain. -/
def prune (width : Nat) (active : Fin (2 ^ width) → Bool) : SelectorTrie width :=
  pruneAt width active width 0 (by omega)

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorTrie
